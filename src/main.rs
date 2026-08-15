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
    guards: Vec<String>,
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
    let mut guards = Vec::new();

    for (line_no, raw) in source.lines().enumerate() {
        let trimmed = raw.trim();
        if let Some(guard) = trimmed.strip_prefix("guard ") {
            let guard = guard.strip_suffix(" else None;").ok_or_else(|| {
                format!("line {}: guards must end with `else None;`", line_no + 1)
            })?;
            guards.push(to_lean_expr(guard));
            let indent = &raw[..raw.len() - raw.trim_start().len()];
            rust.push_str(&format!(
                "{indent}if !({}) {{ return None; }}\n",
                to_rust_expr(guard)
            ));
            continue;
        }
        if let Some(decl) = trimmed.strip_prefix("proof ") {
            let decl = decl.strip_suffix(';').unwrap_or(decl).trim();
            let name_end = decl
                .find([' ', '('])
                .ok_or_else(|| format!("line {}: malformed proof", line_no + 1))?;
            let name = decl[..name_end].to_owned();
            let colon = decl
                .rfind(" : ")
                .ok_or_else(|| format!("line {}: proof needs a conclusion", line_no + 1))?;
            let by = decl[colon + 3..]
                .find(" := by ")
                .ok_or_else(|| format!("line {}: proof must use `:= by`", line_no + 1))?
                + colon
                + 3;
            let conclusion = decl[colon + 3..by].trim().to_owned();
            let header = decl[..colon].trim().to_owned();
            if header.contains(" Prop)") {
                return Err(format!(
                    "line {}: proof hypotheses come only from preceding guards",
                    line_no + 1
                ));
            }
            proofs.push(Proof {
                name,
                header,
                conclusion,
                body: decl[by + 7..].trim().to_owned(),
                guards: guards.clone(),
            });
            continue;
        }
        if trimmed.starts_with("//") || trimmed.is_empty() {
            rust.push_str(raw);
            rust.push('\n');
            continue;
        }
        let (rewritten, found) = rewrite_accesses(raw, line_no + 1)?;
        accesses.extend(found);
        rust.push_str(&rewritten);
        rust.push('\n');
    }
    Ok(Module {
        rust,
        proofs,
        accesses,
    })
}

fn to_lean_expr(expr: &str) -> String {
    expr.replace("input.len()", "input_len")
        .replace("output.len()", "output_len")
        .replace(">=", "≥")
        .replace("<=", "≤")
        .replace("&&", "∧")
}

fn to_rust_expr(expr: &str) -> String {
    expr.replace("input_len", "input.len()")
        .replace("output_len", "output.len()")
        .replace('≥', ">=")
        .replace('≤', "<=")
        .replace('∧', "&&")
}

fn rewrite_accesses(line: &str, line_no: usize) -> Result<(String, Vec<Access>), String> {
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
        let mutable = start > 0 && bytes[start - 1] == b'!';
        if mutable {
            start -= 1;
        }
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
        let Some(rest) = after.strip_prefix(" by ") else {
            return Err(format!(
                "line {line_no}: every array access requires `by <proof>`"
            ));
        };
        let proof_len = rest
            .bytes()
            .take_while(|b| b.is_ascii_alphanumeric() || *b == b'_')
            .count();
        if proof_len == 0 {
            return Err(format!("line {line_no}: missing proof name"));
        }
        let proof = &rest[..proof_len];
        let array_end = if mutable { i - 1 } else { i };
        let array = &line[start..array_end];
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
            proof: proof.into(),
            line: line_no,
        });
        cursor = end + 1 + 4 + proof_len;
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
        out.push_str(&proof.header);
        for (i, guard) in proof.guards.iter().enumerate() {
            out.push_str(&format!(" (h_guard_{i} : {guard})"));
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
    fn rejects_bare_index() {
        assert!(
            parse("fn f(a: &[u8]) { let x = a[0]; }")
                .unwrap_err()
                .contains("requires")
        );
    }

    #[test]
    fn emits_unchecked_access_after_matching_proof() {
        let m = parse("guard a_len > 0 else None;\nproof p (a_len : Nat) : 0 < a_len := by omega;\nfn f(a: &[u8]) -> Option<()> { let _x = a[0] by p; Some(()) }").unwrap();
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
}
