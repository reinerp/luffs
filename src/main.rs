use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

#[derive(Debug)]
struct Proof {
    name: String,
    header: String,
    conclusion: String,
    body: String,
    facts: Vec<String>,
}

#[derive(Debug)]
struct Access {
    array: String,
    subscript: String,
    proof: String,
    line: usize,
}

#[derive(Debug)]
struct Module {
    rust: String,
    proofs: Vec<Proof>,
    accesses: Vec<Access>,
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("luffs: {e}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), String> {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        return Err("usage: luffs <emit|check|build> <source.luffs> [-o PATH]".into());
    }
    let command = &args[1];
    let source = PathBuf::from(&args[2]);
    let output = args
        .windows(2)
        .find(|w| w[0] == "-o")
        .map(|w| PathBuf::from(&w[1]));
    let text = fs::read_to_string(&source).map_err(|e| format!("{}: {e}", source.display()))?;
    let module = parse(&text)?;
    validate(&module)?;

    match command.as_str() {
        "emit" => emit(&source, output.as_deref(), &module),
        "check" => check(&source, &module),
        "build" => build(&source, output.as_deref(), &module),
        _ => Err(format!("unknown command `{command}`")),
    }
}

fn parse(source: &str) -> Result<Module, String> {
    let mut rust = String::new();
    let mut proofs = Vec::new();
    let mut accesses = Vec::new();
    let mut facts = Vec::new();
    let mut nat_vars = Vec::new();
    let mut mutable_arrays = BTreeSet::new();
    let mut pending_if: Option<(Option<String>, bool)> = None;
    let mut pending_while: Option<(String, usize)> = None;
    let mut auto_proof = 0usize;

    for (line_no, raw) in source.lines().enumerate() {
        let trimmed = raw.trim();
        if let Some((condition, old_fact_count)) = &pending_while
            && trimmed == "}"
            && pending_if.is_none()
        {
            facts.truncate(*old_fact_count);
            facts.push(format!("¬ ({condition})"));
            pending_while = None;
        }
        if trimmed.starts_with("fn ") {
            nat_vars.clear();
            mutable_arrays.clear();
            facts.clear();
            for part in trimmed.split(['(', ',', ')']) {
                if let Some((name, ty)) = part.trim().split_once(':') {
                    if ty.contains("&[") || ty.contains("&mut [") {
                        nat_vars.push(format!("{}_len", name.trim()));
                    }
                    if ty.contains("&mut [") {
                        mutable_arrays.insert(name.trim().to_owned());
                    }
                }
            }
        }
        if let Some(rest) = trimmed.strip_prefix("let ") {
            if let Some((name, ty_and_rest)) = rest.split_once(':') {
                let ty = ty_and_rest.trim_start();
                if ty.starts_with("usize") {
                    nat_vars.push(name.trim().trim_start_matches("mut ").to_owned());
                }
            }
        }
        if let Some((condition, diverges)) = &mut pending_if {
            if is_diverging_statement(trimmed) {
                *diverges = true;
            }
            if trimmed == "}" {
                if *diverges && let Some(condition) = condition {
                    facts.push(format!("¬ ({condition})"));
                }
                pending_if = None;
            }
        } else if let Some(condition) = control_condition(trimmed, "if") {
            if trimmed.contains("{ return ") && trimmed.ends_with('}') {
                if fact_supported(condition, &nat_vars) {
                    facts.push(format!("¬ ({})", to_lean_expr(condition)));
                }
            } else if trimmed.ends_with('{') {
                let condition =
                    fact_supported(condition, &nat_vars).then(|| to_lean_expr(condition));
                pending_if = Some((condition, false));
            }
        } else if let Some(condition) = control_condition(trimmed, "while")
            && trimmed.ends_with('{')
            && fact_supported(condition, &nat_vars)
        {
            let condition = to_lean_expr(condition);
            let old_fact_count = facts.len();
            facts.push(condition.clone());
            pending_while = Some((condition, old_fact_count));
        }
        if let Some(decl) = trimmed.strip_prefix("proof ") {
            let decl = decl.strip_suffix(';').unwrap_or(decl).trim();
            let name_end = decl
                .find(':')
                .ok_or_else(|| format!("line {}: malformed proof", line_no + 1))?;
            let name = decl[..name_end].trim().to_owned();
            let rest = decl[name_end + 1..].trim();
            let (conclusion, body) = rest
                .split_once(" by ")
                .map_or((rest, "omega"), |(p, tactic)| (p.trim(), tactic.trim()));
            proofs.push(Proof {
                name,
                header: proof_header(&nat_vars),
                conclusion: to_lean_expr(conclusion),
                body: body.to_owned(),
                facts: facts.clone(),
            });
            continue;
        }
        if trimmed.starts_with("//") || trimmed.is_empty() {
            rust.push_str(raw);
            rust.push('\n');
            continue;
        }
        let (rewritten, found) =
            rewrite_accesses(raw, line_no + 1, &mut auto_proof, &mutable_arrays)?;
        for access in found {
            if access.proof.starts_with("__auto_") {
                proofs.push(Proof {
                    name: access.proof.clone(),
                    header: proof_header(&nat_vars),
                    conclusion: to_lean_expr(&obligation(&access)),
                    body: "omega".to_owned(),
                    facts: facts.clone(),
                });
            }
            accesses.push(access);
        }
        rust.push_str(&rewritten);
        rust.push('\n');
    }
    Ok(Module {
        rust,
        proofs,
        accesses,
    })
}

fn proof_header(vars: &[String]) -> String {
    if vars.is_empty() {
        String::new()
    } else {
        format!(" ({} : Nat)", vars.join(" "))
    }
}

fn control_condition<'a>(line: &'a str, keyword: &str) -> Option<&'a str> {
    let rest = line.strip_prefix(&format!("{keyword} "))?;
    let brace = rest.find('{')?;
    Some(rest[..brace].trim())
}

fn is_diverging_statement(line: &str) -> bool {
    ["return ", "break", "continue", "panic!(", "unreachable!("]
        .iter()
        .any(|prefix| line.starts_with(prefix))
}

fn fact_supported(expr: &str, nat_vars: &[String]) -> bool {
    if expr.contains("::") || expr.contains('&') || expr.contains('|') {
        return false;
    }
    let lean = to_lean_expr(expr);
    lean.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .filter(|word| !word.is_empty() && !word.bytes().all(|b| b.is_ascii_digit()))
        .all(|word| nat_vars.iter().any(|var| var == word))
}

fn to_lean_expr(expr: &str) -> String {
    let mut rewritten = expr.to_owned();
    while let Some(pos) = rewritten.find(".len()") {
        let start = rewritten[..pos]
            .rfind(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .map_or(0, |i| i + 1);
        let name = rewritten[start..pos].to_owned();
        rewritten.replace_range(start..pos + 6, &format!("{name}_len"));
    }
    rewritten
        .replace(">=", "≥")
        .replace("<=", "≤")
        .replace("==", "=")
        .replace("!=", "≠")
        .replace("&&", "∧")
        .replace("||", "∨")
}

fn rewrite_accesses(
    line: &str,
    line_no: usize,
    auto_proof: &mut usize,
    mutable_arrays: &BTreeSet<String>,
) -> Result<(String, Vec<Access>), String> {
    let bytes = line.as_bytes();
    let mut out = String::new();
    let mut found = Vec::new();
    let mut cursor = 0;
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] != b'[' {
            i += 1;
            continue;
        }
        let mut start = i;
        while start > 0 && (bytes[start - 1].is_ascii_alphanumeric() || bytes[start - 1] == b'_') {
            start -= 1;
        }
        if start == i {
            i += 1;
            continue;
        } // array type/literal, not an access
        let Some(rel_end) = line[i + 1..].find(']') else {
            return Err(format!("line {line_no}: unclosed subscript"));
        };
        let end = i + 1 + rel_end;
        let after = &line[end + 1..];
        let (proof, consumed) = if let Some(rest) = after.strip_prefix(" by ") {
            let proof_len = rest
                .bytes()
                .take_while(|b| b.is_ascii_alphanumeric() || *b == b'_')
                .count();
            if proof_len == 0 {
                return Err(format!("line {line_no}: missing proof name"));
            }
            (rest[..proof_len].to_owned(), 4 + proof_len)
        } else {
            let name = format!("__auto_{}", *auto_proof);
            *auto_proof += 1;
            (name, 0)
        };
        let array = &line[start..i];
        let mutable = mutable_arrays.contains(array);
        let subscript = &line[i + 1..end];
        out.push_str(&line[cursor..start]);
        let rust_subscript = if let Some((begin, len)) = subscript.split_once("..+") {
            format!("{begin}..({begin} + {len})")
        } else if let Some((begin, end)) = subscript.split_once("..<") {
            format!("{begin}..{end}")
        } else {
            subscript.to_owned()
        };
        if subscript.contains("..") {
            let method = if mutable {
                "get_unchecked_mut"
            } else {
                "get_unchecked"
            };
            out.push_str(&format!("unsafe {{ {array}.{method}({rust_subscript}) }}"));
        } else {
            let method = if mutable {
                "get_unchecked_mut"
            } else {
                "get_unchecked"
            };
            out.push_str(&format!("unsafe {{ *{array}.{method}({rust_subscript}) }}"));
        }
        found.push(Access {
            array: array.into(),
            subscript: subscript.into(),
            proof,
            line: line_no,
        });
        cursor = end + 1 + consumed;
        i = cursor;
    }
    out.push_str(&line[cursor..]);
    Ok((out, found))
}

fn normalize(s: &str) -> String {
    s.split_whitespace().collect::<String>()
}

fn obligation(a: &Access) -> String {
    if let Some((begin, len)) = a.subscript.split_once("..+") {
        format!("{begin} + {len} ≤ {}_len", a.array)
    } else if let Some((begin, end)) = a.subscript.split_once("..<") {
        format!("{begin} ≤ {end} ∧ {end} ≤ {}_len", a.array)
    } else {
        format!("{} < {}_len", a.subscript, a.array)
    }
}

fn validate(module: &Module) -> Result<(), String> {
    let mut names = BTreeSet::new();
    let mut proofs = BTreeMap::new();
    for p in &module.proofs {
        if !names.insert(&p.name) {
            return Err(format!("duplicate proof `{}`", p.name));
        }
        proofs.insert(p.name.as_str(), p);
    }
    for a in &module.accesses {
        let p = proofs
            .get(a.proof.as_str())
            .ok_or_else(|| format!("line {}: unknown proof `{}`", a.line, a.proof))?;
        let expected = obligation(a);
        if normalize(&p.conclusion) != normalize(&expected) {
            return Err(format!(
                "line {}: proof `{}` concludes `{}`, expected `{expected}`",
                a.line, a.proof, p.conclusion
            ));
        }
    }
    for forbidden in ["struct ", "enum ", "Vec<", "String"] {
        if module.rust.contains(forbidden) {
            return Err(format!("unsupported Rust feature `{}`", forbidden.trim()));
        }
    }
    Ok(())
}

fn lean(module: &Module) -> String {
    let mut out = String::from(
        "import Init.Omega\n\nset_option autoImplicit false\n\nnamespace LuffsGenerated\n\n",
    );
    for proof in &module.proofs {
        out.push_str("theorem ");
        out.push_str(&proof.name);
        out.push_str(&proof.header);
        for (i, fact) in proof.facts.iter().enumerate() {
            out.push_str(&format!(" (h_fact_{i} : {fact})"));
        }
        out.push_str(" : ");
        out.push_str(&proof.conclusion);
        out.push_str(" := by ");
        out.push_str(&proof.body);
        out.push_str("\n\n");
    }
    out.push_str("end LuffsGenerated\n");
    out
}

fn paths(source: &Path) -> (PathBuf, PathBuf) {
    let stem = source.file_stem().unwrap_or_default().to_string_lossy();
    (
        PathBuf::from("build").join(format!("{stem}.rs")),
        PathBuf::from("build").join(format!("{stem}.lean")),
    )
}

fn write_outputs(source: &Path, module: &Module) -> Result<(PathBuf, PathBuf), String> {
    let (rs, lean_path) = paths(source);
    fs::create_dir_all("build").map_err(|e| e.to_string())?;
    fs::write(&rs, &module.rust).map_err(|e| e.to_string())?;
    fs::write(&lean_path, lean(module)).map_err(|e| e.to_string())?;
    Ok((rs, lean_path))
}

fn emit(source: &Path, output: Option<&Path>, module: &Module) -> Result<(), String> {
    let (rs, lean_path) = write_outputs(source, module)?;
    if let Some(path) = output {
        fs::copy(&rs, path).map_err(|e| e.to_string())?;
    }
    println!("Rust: {}\nLean: {}", rs.display(), lean_path.display());
    Ok(())
}

fn run_tool(mut command: Command, name: &str) -> Result<(), String> {
    let status = command
        .status()
        .map_err(|e| format!("could not run {name}: {e}"))?;
    if status.success() {
        Ok(())
    } else {
        Err(format!("{name} rejected generated output"))
    }
}

fn check(source: &Path, module: &Module) -> Result<(), String> {
    let (_, lean_path) = write_outputs(source, module)?;
    let mut command = Command::new("lake");
    command.args(["env", "lean"]).arg(lean_path);
    run_tool(command, "Lean")
}

fn build(source: &Path, output: Option<&Path>, module: &Module) -> Result<(), String> {
    check(source, module)?;
    let (rs, _) = paths(source);
    let binary = output
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("build/program"));
    let mut command = Command::new("rustc");
    command
        .arg("--edition=2024")
        .arg("-O")
        .arg(rs)
        .arg("-o")
        .arg(binary);
    run_tool(command, "rustc")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bare_index_gets_an_omega_obligation() {
        let m = parse(
            "fn f(input: &[u8]) -> Option<u8> {\nif input.len() == 0 { return None; }\nSome(input[0])\n}",
        )
        .unwrap();
        validate(&m).unwrap();
        assert_eq!(m.proofs[0].body, "omega");
        assert_eq!(m.proofs[0].conclusion, "0 < input_len");
    }

    #[test]
    fn emits_unchecked_access_after_matching_proof() {
        let m = parse("fn f(a: &[u8]) -> Option<()> {\nif a.len() == 0 { return None; }\nproof p: 0 < a.len();\nlet _x = a[0] by p;\nSome(())\n}").unwrap();
        validate(&m).unwrap();
        assert!(m.rust.contains("unsafe { *a.get_unchecked(0) }"));
    }

    #[test]
    fn distinguishes_slice_conventions() {
        let a = Access {
            array: "a".into(),
            subscript: "b..+n".into(),
            proof: "p".into(),
            line: 1,
        };
        let b = Access {
            array: "a".into(),
            subscript: "b..<e".into(),
            proof: "q".into(),
            line: 1,
        };
        assert_eq!(obligation(&a), "b + n ≤ a_len");
        assert_eq!(obligation(&b), "b ≤ e ∧ e ≤ a_len");
    }

    #[test]
    fn loop_condition_is_a_fact_inside_the_body() {
        let m = parse(
            "fn f(input: &[u8]) -> Option<()> {\nlet mut i: usize = 0;\nwhile i < input.len() {\nlet _x = input[i];\ni += 1;\n}\nSome(())\n}",
        )
        .unwrap();
        assert_eq!(m.proofs[0].facts, ["i < input_len"]);
    }
}
