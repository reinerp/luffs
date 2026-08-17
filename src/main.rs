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
    scalar_models: Vec<ScalarModel>,
    array_models: Vec<ArrayModel>,
    read_models: Vec<ReadModel>,
    copy_models: Vec<CopyModel>,
    tlsf_insert_models: Vec<TlsfInsertModel>,
    tlsf_remove_models: Vec<TlsfRemoveModel>,
    tlsf_find_fit_models: Vec<TlsfFindFitModel>,
    tlsf_find_nonempty_bin_models: Vec<TlsfFindNonemptyBinModel>,
    tlsf_take_candidate_models: Vec<TlsfTakeCandidateModel>,
    tlsf_find_nonempty_class_models: Vec<TlsfFindNonemptyClassModel>,
    tlsf_take_candidate_class_models: Vec<TlsfTakeCandidateModel>,
    tlsf_mark_free_models: Vec<TlsfMarkFreeModel>,
    tlsf_classify_size_models: Vec<TlsfClassifySizeModel>,
    tlsf_insert_class_models: Vec<TlsfInsertClassModel>,
    tlsf_remove_class_models: Vec<TlsfInsertClassModel>,
    tlsf_deallocate_uncoalesced_models: Vec<TlsfDeallocateUncoalescedModel>,
    tlsf_coalesce_physical_models: Vec<TlsfCoalescePhysicalModel>,
    tlsf_coalesce_class_models: Vec<TlsfCoalescePhysicalModel>,
    tlsf_coalesce_if_possible_models: Vec<TlsfCoalescePhysicalModel>,
    tlsf_deallocate_models: Vec<TlsfCoalescePhysicalModel>,
}

#[derive(Debug)]
struct ScalarModel {
    name: String,
    params: Vec<String>,
    guards: Vec<String>,
    lets: Vec<(String, String)>,
    result: String,
    refines: Option<String>,
}

#[derive(Debug)]
struct ArrayModel {
    name: String,
    array: String,
    params: Vec<(String, String)>,
    guards: Vec<String>,
    lets: Vec<(String, String)>,
    assignment: (String, String),
    result: String,
    returns_unit: bool,
    refines: Option<String>,
}

#[derive(Debug)]
struct ReadModel {
    name: String,
    params: Vec<(String, String)>,
    guards: Vec<String>,
    lets: Vec<(String, String)>,
    result: String,
    result_type: String,
    refines: Option<String>,
}

#[derive(Debug)]
struct CopyModel {
    name: String,
    source: String,
    destination: String,
    len: String,
    guards: Vec<String>,
    refines: Option<String>,
}

#[derive(Debug)]
struct TlsfInsertModel {
    name: String,
    refines: String,
}

#[derive(Debug)]
struct TlsfRemoveModel {
    name: String,
    refines: String,
}

#[derive(Debug)]
struct TlsfFindFitModel {
    name: String,
    refines: String,
}

#[derive(Debug)]
struct TlsfFindNonemptyBinModel {
    name: String,
    refines: String,
}

#[derive(Debug)]
struct TlsfTakeCandidateModel {
    name: String,
    refines: String,
}

#[derive(Debug)]
struct TlsfFindNonemptyClassModel {
    name: String,
    refines: String,
}

#[derive(Debug)]
struct TlsfMarkFreeModel {
    name: String,
    refines: String,
}

#[derive(Debug)]
struct TlsfClassifySizeModel {
    name: String,
    refines: String,
}

#[derive(Debug)]
struct TlsfInsertClassModel {
    name: String,
    refines: String,
}

#[derive(Debug)]
struct TlsfDeallocateUncoalescedModel {
    name: String,
    refines: String,
}

#[derive(Debug)]
struct TlsfCoalescePhysicalModel {
    name: String,
    refines: String,
}

#[derive(Debug)]
enum ControlScope {
    If {
        condition: Option<String>,
        diverges: bool,
        old_fact_count: usize,
        body_depth: usize,
    },
    While {
        condition: String,
        old_fact_count: usize,
        body_depth: usize,
    },
}

impl ControlScope {
    fn body_depth(&self) -> usize {
        match self {
            Self::If { body_depth, .. } | Self::While { body_depth, .. } => *body_depth,
        }
    }
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
    let mut control_scopes = Vec::new();
    let mut brace_depth = 0usize;
    let mut auto_proof = 0usize;
    let mut overflow_proof = 0usize;

    for (line_no, raw) in logical_lines(source)? {
        let raw = raw.as_str();
        let trimmed = raw.trim();
        if trimmed.starts_with("fn ") {
            nat_vars.clear();
            mutable_arrays.clear();
            facts.clear();
            control_scopes.clear();
            brace_depth = 0;
            for part in trimmed.split(['(', ',', ')']) {
                if let Some((name, ty)) = part.trim().split_once(':') {
                    if ty.contains("&[") || ty.contains("&mut [") {
                        nat_vars.push(format!("{}_len", name.trim()));
                    } else if ty.trim().starts_with("usize") {
                        nat_vars.push(name.trim().to_owned());
                    }
                    if ty.contains("&mut [") {
                        mutable_arrays.insert(name.trim().to_owned());
                    }
                }
            }
        }
        if let Some((name, expression)) = usize_let(trimmed) {
            if arithmetic_expression(expression) {
                let conclusion = overflow_obligation(expression)?;
                proofs.push(Proof {
                    name: format!("__overflow_{overflow_proof}"),
                    header: proof_header(&nat_vars),
                    conclusion,
                    body: "omega".to_owned(),
                    facts: proof_facts(&nat_vars, &facts),
                });
                overflow_proof += 1;
                facts.push(format!(
                    "{} = {}",
                    lean_ident(name),
                    to_lean_expr(expression)
                ));
                facts.push(overflow_obligation(expression)?);
            }
            nat_vars.push(name.to_owned());
        }
        if is_diverging_statement(trimmed)
            && let Some(ControlScope::If { diverges, .. }) = control_scopes.last_mut()
        {
            *diverges = true;
        }
        if trimmed.starts_with("} else {")
            && let Some(ControlScope::If {
                condition,
                diverges,
                old_fact_count,
                ..
            }) = control_scopes.last_mut()
        {
            facts.truncate(*old_fact_count);
            if let Some(condition) = condition {
                facts.push(format!("¬ ({condition})"));
            }
            *diverges = false;
        } else if let Some(condition) = control_condition(trimmed, "if") {
            if trimmed.contains("{ return ") && trimmed.ends_with('}') {
                if fact_supported(condition, &nat_vars) {
                    facts.push(format!("¬ ({})", to_lean_expr(condition)));
                }
            } else if trimmed.ends_with('{') {
                let condition =
                    fact_supported(condition, &nat_vars).then(|| to_lean_expr(condition));
                let old_fact_count = facts.len();
                if let Some(condition) = &condition {
                    facts.push(condition.clone());
                }
                control_scopes.push(ControlScope::If {
                    condition,
                    diverges: false,
                    old_fact_count,
                    body_depth: brace_depth + 1,
                });
            }
        } else if let Some(condition) = control_condition(trimmed, "while")
            && trimmed.ends_with('{')
            && fact_supported(condition, &nat_vars)
        {
            let condition = to_lean_expr(condition);
            let old_fact_count = facts.len();
            facts.push(condition.clone());
            control_scopes.push(ControlScope::While {
                condition,
                old_fact_count,
                body_depth: brace_depth + 1,
            });
        }
        if let Some(decl) = trimmed.strip_prefix("proof ") {
            let decl = decl.strip_suffix(';').unwrap_or(decl).trim();
            let name_end = decl
                .find(':')
                .ok_or_else(|| format!("line {line_no}: malformed proof"))?;
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
                facts: proof_facts(&nat_vars, &facts),
            });
            continue;
        }
        if trimmed.starts_with("//") || trimmed.is_empty() {
            rust.push_str(raw);
            rust.push('\n');
            continue;
        }
        let (rewritten, found) = rewrite_accesses(raw, line_no, &mut auto_proof, &mutable_arrays)?;
        for access in found {
            if access.proof.starts_with("__auto_") {
                proofs.push(Proof {
                    name: access.proof.clone(),
                    header: proof_header(&nat_vars),
                    conclusion: to_lean_expr(&obligation(&access)),
                    body: "omega".to_owned(),
                    facts: proof_facts(&nat_vars, &facts),
                });
            }
            accesses.push(access);
        }
        rust.push_str(&rewritten);
        rust.push('\n');

        let opens = raw.bytes().filter(|byte| *byte == b'{').count();
        let closes = raw.bytes().filter(|byte| *byte == b'}').count();
        brace_depth = brace_depth.saturating_add(opens).saturating_sub(closes);
        while control_scopes
            .last()
            .is_some_and(|scope| scope.body_depth() > brace_depth)
        {
            match control_scopes.pop().expect("scope exists") {
                ControlScope::If {
                    condition,
                    diverges,
                    old_fact_count,
                    ..
                } => {
                    facts.truncate(old_fact_count);
                    if diverges && let Some(condition) = condition {
                        facts.push(format!("¬ ({condition})"));
                    }
                }
                ControlScope::While {
                    condition,
                    old_fact_count,
                    ..
                } => {
                    facts.truncate(old_fact_count);
                    facts.push(format!("¬ ({condition})"));
                }
            }
        }
    }
    Ok(Module {
        rust,
        proofs,
        accesses,
        scalar_models: parse_scalar_models(source),
        array_models: parse_array_models(source),
        read_models: parse_read_models(source),
        copy_models: parse_copy_models(source),
        tlsf_insert_models: parse_tlsf_insert_models(source),
        tlsf_remove_models: parse_tlsf_remove_models(source),
        tlsf_find_fit_models: parse_tlsf_find_fit_models(source),
        tlsf_find_nonempty_bin_models: parse_tlsf_find_nonempty_bin_models(source),
        tlsf_take_candidate_models: parse_tlsf_take_candidate_models(source),
        tlsf_find_nonempty_class_models: parse_tlsf_find_nonempty_class_models(source),
        tlsf_take_candidate_class_models: parse_tlsf_take_candidate_class_models(source),
        tlsf_mark_free_models: parse_tlsf_mark_free_models(source),
        tlsf_classify_size_models: parse_tlsf_classify_size_models(source),
        tlsf_insert_class_models: parse_tlsf_insert_class_models(source),
        tlsf_remove_class_models: parse_tlsf_remove_class_models(source),
        tlsf_deallocate_uncoalesced_models: parse_tlsf_deallocate_uncoalesced_models(source),
        tlsf_coalesce_physical_models: parse_tlsf_coalesce_physical_models(source),
        tlsf_coalesce_class_models: parse_tlsf_coalesce_class_models(source),
        tlsf_coalesce_if_possible_models: parse_tlsf_coalesce_if_possible_models(source),
        tlsf_deallocate_models: parse_tlsf_deallocate_models(source),
    })
}

fn parse_scalar_models(source: &str) -> Vec<ScalarModel> {
    #[derive(Default)]
    struct Pending {
        name: String,
        params: Vec<String>,
        guards: Vec<String>,
        lets: Vec<(String, String)>,
        result: Option<String>,
        depth: usize,
        eligible: bool,
        refines: Option<String>,
    }

    let mut models = Vec::new();
    let mut pending: Option<Pending> = None;
    let mut next_refinement = None;
    for raw in source.lines() {
        let trimmed = raw.trim();
        if pending.is_none()
            && let Some(target) = trimmed.strip_prefix("// refines ")
        {
            next_refinement = Some(target.trim().to_owned());
            continue;
        }
        if pending.is_none() && trimmed.starts_with("fn ") {
            let Some(open) = trimmed.find('(') else {
                continue;
            };
            let Some(close) = trimmed[open + 1..]
                .find(')')
                .map(|offset| open + 1 + offset)
            else {
                continue;
            };
            if !trimmed[close + 1..].contains("-> Option<usize>") {
                continue;
            }
            let name = trimmed[3..open].trim().to_owned();
            let mut params = Vec::new();
            let mut eligible = true;
            for param in trimmed[open + 1..close].split(',') {
                let Some((name, ty)) = param.split_once(':') else {
                    eligible = false;
                    break;
                };
                if ty.trim() != "usize" {
                    eligible = false;
                    break;
                }
                params.push(name.trim().to_owned());
            }
            pending = Some(Pending {
                name,
                params,
                depth: 1,
                eligible,
                refines: next_refinement.take(),
                ..Pending::default()
            });
            continue;
        }

        let Some(model) = pending.as_mut() else {
            continue;
        };
        if trimmed.starts_with("//") || trimmed.is_empty() {
            continue;
        }
        if let Some(condition) = control_condition(trimmed, "if")
            && trimmed.contains("{ return None; }")
        {
            model.guards.push(to_lean_expr(condition));
        } else if let Some((name, expression)) = usize_let(trimmed) {
            model
                .lets
                .push((lean_ident(name), to_lean_expr(expression)));
        } else if let Some(result) = trimmed
            .strip_prefix("Some(")
            .and_then(|rest| rest.strip_suffix(')'))
            .or_else(|| {
                trimmed
                    .strip_prefix("return Some(")
                    .and_then(|rest| rest.strip_suffix(");"))
            })
        {
            model.result = Some(to_lean_expr(result));
        } else if trimmed != "}" {
            model.eligible = false;
        }

        let opens = raw.bytes().filter(|byte| *byte == b'{').count();
        let closes = raw.bytes().filter(|byte| *byte == b'}').count();
        model.depth = model.depth.saturating_add(opens).saturating_sub(closes);
        if model.depth == 0 {
            let model = pending.take().expect("pending model exists");
            if model.eligible
                && let Some(result) = model.result
            {
                models.push(ScalarModel {
                    name: model.name,
                    params: model.params,
                    guards: model.guards,
                    lets: model.lets,
                    result,
                    refines: model.refines,
                });
            }
        }
    }
    models
}

fn model_expr(expr: &str, array: &str) -> String {
    to_lean_expr(expr).replace(&format!("{array}_len"), &format!("{array}.length"))
}

fn parse_array_models(source: &str) -> Vec<ArrayModel> {
    #[derive(Default)]
    struct Pending {
        name: String,
        array: String,
        params: Vec<(String, String)>,
        guards: Vec<String>,
        lets: Vec<(String, String)>,
        assignment: Option<(String, String)>,
        result: Option<String>,
        returns_unit: bool,
        refines: Option<String>,
        depth: usize,
        eligible: bool,
    }

    let mut models = Vec::new();
    let mut pending: Option<Pending> = None;
    let mut next_refinement = None;
    for raw in source.lines() {
        let trimmed = raw.trim();
        if pending.is_none()
            && let Some(target) = trimmed.strip_prefix("// refines ")
        {
            next_refinement = Some(target.trim().to_owned());
            continue;
        }
        if pending.is_none() && trimmed.starts_with("fn ") {
            let Some(open) = trimmed.find('(') else {
                continue;
            };
            let Some(close) = trimmed[open + 1..]
                .find(')')
                .map(|offset| open + 1 + offset)
            else {
                continue;
            };
            let return_text = &trimmed[close + 1..];
            let returns_unit = return_text.contains("-> Option<()>");
            if !returns_unit && !return_text.contains("-> Option<usize>") {
                next_refinement = None;
                continue;
            }
            let name = trimmed[3..open].trim().to_owned();
            let mut array = None;
            let mut params = Vec::new();
            let mut eligible = true;
            for param in trimmed[open + 1..close].split(',') {
                let Some((name, ty)) = param.split_once(':') else {
                    eligible = false;
                    break;
                };
                let name = name.trim().to_owned();
                match ty.trim() {
                    "&mut [u8]" => {
                        if array.replace(name.clone()).is_some() {
                            eligible = false;
                        }
                        params.push((name, "List (Fin 256)".to_owned()));
                    }
                    "usize" => params.push((name, "Nat".to_owned())),
                    "u8" => params.push((name, "Fin 256".to_owned())),
                    _ => eligible = false,
                }
            }
            let Some(array) = array else {
                next_refinement = None;
                continue;
            };
            pending = Some(Pending {
                name,
                array,
                params,
                refines: next_refinement.take(),
                returns_unit,
                depth: 1,
                eligible,
                ..Pending::default()
            });
            continue;
        }

        let Some(model) = pending.as_mut() else {
            continue;
        };
        if trimmed.starts_with("//") || trimmed.is_empty() {
            continue;
        }
        if let Some(condition) = control_condition(trimmed, "if")
            && trimmed.contains("{ return None; }")
        {
            model.guards.push(model_expr(condition, &model.array));
        } else if let Some((name, expression)) = usize_let(trimmed) {
            model
                .lets
                .push((lean_ident(name), model_expr(expression, &model.array)));
        } else if let Some(statement) = trimmed.strip_suffix(';')
            && let Some((left, right)) = statement.split_once(" = ")
            && left.starts_with(&format!("{}[", model.array))
            && left.ends_with(']')
        {
            let index = &left[model.array.len() + 1..left.len() - 1];
            model.assignment = Some((
                model_expr(index, &model.array),
                model_expr(right, &model.array),
            ));
        } else if let Some(result) = trimmed
            .strip_prefix("Some(")
            .and_then(|rest| rest.strip_suffix(')'))
        {
            model.result = Some(model_expr(result, &model.array));
        } else if trimmed != "}" {
            model.eligible = false;
        }

        let opens = raw.bytes().filter(|byte| *byte == b'{').count();
        let closes = raw.bytes().filter(|byte| *byte == b'}').count();
        model.depth = model.depth.saturating_add(opens).saturating_sub(closes);
        if model.depth == 0 {
            let model = pending.take().expect("pending model exists");
            if model.eligible
                && let (Some(assignment), Some(result)) = (model.assignment, model.result)
            {
                models.push(ArrayModel {
                    name: model.name,
                    array: model.array,
                    params: model.params,
                    guards: model.guards,
                    lets: model.lets,
                    assignment,
                    result,
                    returns_unit: model.returns_unit,
                    refines: model.refines,
                });
            }
        }
    }
    models
}

fn read_result_expr(expr: &str, array: &str) -> String {
    let expression = model_expr(expr, array);
    if let Some(subscript) = expression
        .strip_prefix(&format!("{array}["))
        .and_then(|rest| rest.strip_suffix(']'))
        && let Some((begin, end)) = subscript.split_once("..<")
    {
        return format!("some (({array}.drop {begin}).take ({end} - {begin}))");
    }
    if expression.starts_with(&format!("{array}[")) && expression.ends_with(']') {
        format!("{expression}?")
    } else {
        format!("some ({expression})")
    }
}

fn parse_read_models(source: &str) -> Vec<ReadModel> {
    #[derive(Default)]
    struct Pending {
        name: String,
        array: String,
        params: Vec<(String, String)>,
        guards: Vec<String>,
        lets: Vec<(String, String)>,
        result: Option<String>,
        result_type: String,
        refines: Option<String>,
        depth: usize,
        eligible: bool,
    }

    let mut models = Vec::new();
    let mut pending: Option<Pending> = None;
    let mut next_refinement = None;
    for raw in source.lines() {
        let trimmed = raw.trim();
        if pending.is_none()
            && let Some(target) = trimmed.strip_prefix("// refines ")
        {
            next_refinement = Some(target.trim().to_owned());
            continue;
        }
        if pending.is_none() && trimmed.starts_with("fn ") {
            let Some(open) = trimmed.find('(') else {
                continue;
            };
            let Some(close) = trimmed[open + 1..].find(')').map(|n| open + 1 + n) else {
                continue;
            };
            let return_text = &trimmed[close + 1..];
            let result_type = if return_text.contains("-> Option<u8>") {
                "Fin 256"
            } else if return_text.contains("-> Option<&[u8]>")
                || return_text.contains("-> Option<&mut [u8]>")
            {
                "List (Fin 256)"
            } else {
                next_refinement = None;
                continue;
            };
            let mut array = None;
            let mut params = Vec::new();
            let mut eligible = true;
            for param in trimmed[open + 1..close].split(',') {
                let Some((name, ty)) = param.split_once(':') else {
                    eligible = false;
                    break;
                };
                let source_name = name.trim().to_owned();
                let name = lean_ident(&source_name);
                match ty.trim() {
                    "&[u8]" | "&mut [u8]" => {
                        if array.replace(source_name).is_some() {
                            eligible = false;
                        }
                        params.push((name, "List (Fin 256)".to_owned()));
                    }
                    "usize" => params.push((name, "Nat".to_owned())),
                    _ => eligible = false,
                }
            }
            let Some(array) = array else {
                next_refinement = None;
                continue;
            };
            pending = Some(Pending {
                name: trimmed[3..open].trim().to_owned(),
                array,
                params,
                refines: next_refinement.take(),
                result_type: result_type.to_owned(),
                depth: 1,
                eligible,
                ..Pending::default()
            });
            continue;
        }

        let Some(model) = pending.as_mut() else {
            continue;
        };
        if trimmed.starts_with("//") || trimmed.is_empty() {
            continue;
        }
        if let Some(condition) = control_condition(trimmed, "if")
            && trimmed.contains("{ return None; }")
        {
            model.guards.push(model_expr(condition, &model.array));
        } else if let Some((name, expression)) = usize_let(trimmed) {
            model
                .lets
                .push((lean_ident(name), model_expr(expression, &model.array)));
        } else if let Some(result) = trimmed
            .strip_prefix("Some(")
            .and_then(|rest| rest.strip_suffix(')'))
        {
            model.result = Some(read_result_expr(result, &model.array));
        } else if trimmed != "}" {
            model.eligible = false;
        }

        let opens = raw.bytes().filter(|byte| *byte == b'{').count();
        let closes = raw.bytes().filter(|byte| *byte == b'}').count();
        model.depth = model.depth.saturating_add(opens).saturating_sub(closes);
        if model.depth == 0 {
            let model = pending.take().expect("pending model exists");
            if model.eligible
                && let Some(result) = model.result
            {
                models.push(ReadModel {
                    name: model.name,
                    params: model.params,
                    guards: model.guards,
                    lets: model.lets,
                    result,
                    result_type: model.result_type,
                    refines: model.refines,
                });
            }
        }
    }
    models
}

fn parse_copy_models(source: &str) -> Vec<CopyModel> {
    #[derive(Default)]
    struct Pending {
        name: String,
        source: String,
        destination: String,
        len: String,
        guards: Vec<String>,
        saw_source_slice: bool,
        saw_destination_slice: bool,
        saw_copy: bool,
        saw_result: bool,
        refines: Option<String>,
        depth: usize,
        eligible: bool,
    }

    let mut models = Vec::new();
    let mut pending: Option<Pending> = None;
    let mut next_refinement = None;
    for raw in source.lines() {
        let trimmed = raw.trim();
        if pending.is_none()
            && let Some(target) = trimmed.strip_prefix("// refines ")
        {
            next_refinement = Some(target.trim().to_owned());
            continue;
        }
        if pending.is_none() && trimmed.starts_with("fn ") {
            let Some(open) = trimmed.find('(') else {
                continue;
            };
            let Some(close) = trimmed[open + 1..].find(')').map(|n| open + 1 + n) else {
                continue;
            };
            if !trimmed[close + 1..].contains("-> Option<()>") {
                next_refinement = None;
                continue;
            }
            let params = trimmed[open + 1..close]
                .split(',')
                .filter_map(|param| param.split_once(':'))
                .map(|(name, ty)| (name.trim(), ty.trim()))
                .collect::<Vec<_>>();
            let source = params.iter().find(|(_, ty)| *ty == "&[u8]");
            let destination = params.iter().find(|(_, ty)| *ty == "&mut [u8]");
            let len = params.iter().find(|(_, ty)| *ty == "usize");
            let (Some(source), Some(destination), Some(len)) = (source, destination, len) else {
                next_refinement = None;
                continue;
            };
            pending = Some(Pending {
                name: trimmed[3..open].trim().to_owned(),
                source: source.0.to_owned(),
                destination: destination.0.to_owned(),
                len: lean_ident(len.0),
                refines: next_refinement.take(),
                depth: 1,
                eligible: params.len() == 3,
                ..Pending::default()
            });
            continue;
        }

        let Some(model) = pending.as_mut() else {
            continue;
        };
        if trimmed.starts_with("//") || trimmed.is_empty() {
            continue;
        }
        if let Some(condition) = control_condition(trimmed, "if")
            && trimmed.contains("{ return None; }")
        {
            let expression = to_lean_expr(condition)
                .replace(
                    &format!("{}_len", model.source),
                    &format!("{}.length", model.source),
                )
                .replace(
                    &format!("{}_len", model.destination),
                    &format!("{}.length", model.destination),
                );
            model.guards.push(expression);
        } else if trimmed.starts_with("let from: &[u8] = ") {
            model.saw_source_slice =
                trimmed.contains(&format!("{}[0..<{}]", model.source, model.len));
        } else if trimmed.starts_with("let to: &mut [u8] = ") {
            model.saw_destination_slice =
                trimmed.contains(&format!("{}[0..<{}]", model.destination, model.len));
        } else if trimmed == "to.copy_from_slice(from);" {
            model.saw_copy = true;
        } else if trimmed == "Some(())" {
            model.saw_result = true;
        } else if trimmed != "}" {
            model.eligible = false;
        }

        let opens = raw.bytes().filter(|byte| *byte == b'{').count();
        let closes = raw.bytes().filter(|byte| *byte == b'}').count();
        model.depth = model.depth.saturating_add(opens).saturating_sub(closes);
        if model.depth == 0 {
            let model = pending.take().expect("pending model exists");
            if model.eligible
                && model.saw_source_slice
                && model.saw_destination_slice
                && model.saw_copy
                && model.saw_result
            {
                models.push(CopyModel {
                    name: model.name,
                    source: model.source,
                    destination: model.destination,
                    len: model.len,
                    guards: model.guards,
                    refines: model.refines,
                });
            }
        }
    }
    models
}

fn parse_tlsf_insert_models(source: &str) -> Vec<TlsfInsertModel> {
    let lines = source.lines().collect::<Vec<_>>();
    let mut models = Vec::new();
    for (index, raw) in lines.iter().enumerate() {
        let signature = raw.trim();
        if !signature.starts_with("fn tlsf_insert(") {
            continue;
        }
        let Some(annotation) = index.checked_sub(1).and_then(|i| lines.get(i)) else {
            continue;
        };
        let Some(target) = annotation.trim().strip_prefix("// refines ") else {
            continue;
        };
        let mut depth = signature.matches('{').count() - signature.matches('}').count();
        let mut body = Vec::new();
        for line in &lines[index + 1..] {
            let trimmed = line.trim();
            depth += trimmed.matches('{').count();
            depth = depth.saturating_sub(trimmed.matches('}').count());
            if depth == 0 {
                break;
            }
            if !trimmed.is_empty() {
                body.push(trimmed);
            }
        }
        let required = [
            "if bin >= heads.len() { return None; }",
            "if block >= next.len() { return None; }",
            "if block >= previous.len() { return None; }",
            "let old_head: usize = heads[bin];",
            "next[block] = old_head;",
            "previous[block] = next.len();",
            "if old_head < previous.len() {",
            "previous[old_head] = block;",
            "heads[bin] = block;",
            "Some(())",
        ];
        let mut position = 0;
        let valid = required.iter().all(|expected| {
            if let Some(offset) = body[position..].iter().position(|line| line == expected) {
                position += offset + 1;
                true
            } else {
                false
            }
        });
        if valid {
            models.push(TlsfInsertModel {
                name: "tlsf_insert".to_owned(),
                refines: target.trim().to_owned(),
            });
        }
    }
    models
}

fn parse_tlsf_remove_models(source: &str) -> Vec<TlsfRemoveModel> {
    let lines = source.lines().collect::<Vec<_>>();
    let mut models = Vec::new();
    for (index, raw) in lines.iter().enumerate() {
        if !raw.trim().starts_with("fn tlsf_remove(") {
            continue;
        }
        let Some(target) = index
            .checked_sub(1)
            .and_then(|i| lines.get(i))
            .and_then(|line| line.trim().strip_prefix("// refines "))
        else {
            continue;
        };
        let end = lines[index + 1..]
            .iter()
            .position(|line| line.trim().starts_with("fn "))
            .map_or(lines.len(), |offset| index + 1 + offset);
        let body = lines[index + 1..end]
            .iter()
            .map(|line| line.trim())
            .collect::<Vec<_>>();
        let required = [
            "if bin >= heads.len() { return None; }",
            "if block >= next.len() { return None; }",
            "if block >= previous.len() { return None; }",
            "let successor: usize = next[block];",
            "let predecessor: usize = previous[block];",
            "if predecessor >= next.len() {",
            "heads[bin] = successor;",
            "if predecessor < next.len() {",
            "next[predecessor] = successor;",
            "if successor < previous.len() {",
            "previous[successor] = predecessor;",
            "next[block] = next.len();",
            "previous[block] = previous.len();",
            "Some(())",
        ];
        let mut position = 0;
        let valid = required.iter().all(|expected| {
            if let Some(offset) = body[position..].iter().position(|line| line == expected) {
                position += offset + 1;
                true
            } else {
                false
            }
        });
        if valid {
            models.push(TlsfRemoveModel {
                name: "tlsf_remove".to_owned(),
                refines: target.trim().to_owned(),
            });
        }
    }
    models
}

fn parse_tlsf_find_fit_models(source: &str) -> Vec<TlsfFindFitModel> {
    let lines = source.lines().collect::<Vec<_>>();
    let Some(index) = lines
        .iter()
        .position(|line| line.trim().starts_with("fn tlsf_find_fit("))
    else {
        return Vec::new();
    };
    let Some(target) = index
        .checked_sub(1)
        .and_then(|i| lines.get(i))
        .and_then(|line| line.trim().strip_prefix("// refines "))
    else {
        return Vec::new();
    };
    let end = lines[index + 1..]
        .iter()
        .position(|line| line.trim().starts_with("fn "))
        .map_or(lines.len(), |offset| index + 1 + offset);
    let body = lines[index + 1..end]
        .iter()
        .map(|line| line.trim())
        .collect::<Vec<_>>();
    let required = [
        "let mut block: usize = 0;",
        "while block < sizes.len() {",
        "if block >= is_free.len() { return None; }",
        "let free: u8 = is_free[block];",
        "let bytes: usize = sizes[block];",
        "if free != 0 {",
        "if request <= bytes {",
        "return Some(block);",
        "let next_block: usize = block + 1;",
        "block = next_block;",
        "None",
    ];
    let mut position = 0;
    if required.iter().all(|expected| {
        if let Some(offset) = body[position..].iter().position(|line| line == expected) {
            position += offset + 1;
            true
        } else {
            false
        }
    }) {
        vec![TlsfFindFitModel {
            name: "tlsf_find_fit".to_owned(),
            refines: target.trim().to_owned(),
        }]
    } else {
        Vec::new()
    }
}

fn parse_tlsf_find_nonempty_bin_models(source: &str) -> Vec<TlsfFindNonemptyBinModel> {
    let lines = source.lines().collect::<Vec<_>>();
    let Some(index) = lines
        .iter()
        .position(|line| line.trim().starts_with("fn tlsf_find_nonempty_bin("))
    else {
        return Vec::new();
    };
    let Some(target) = index
        .checked_sub(1)
        .and_then(|i| lines.get(i))
        .and_then(|line| line.trim().strip_prefix("// refines "))
    else {
        return Vec::new();
    };
    let end = lines[index + 1..]
        .iter()
        .position(|line| line.trim().starts_with("fn "))
        .map_or(lines.len(), |offset| index + 1 + offset);
    let body = lines[index + 1..end]
        .iter()
        .map(|line| line.trim())
        .collect::<Vec<_>>();
    let required = [
        "let mut word: usize = start_bin >> 6;",
        "let bit = start_bin & 63;",
        "if word >= nonempty.len() { return None; }",
        "let first_bitmap: u64 = nonempty[word];",
        "let first_masked = first_bitmap & (u64::MAX << bit);",
        "if first_masked != 0 {",
        "let offset: usize = first_masked.trailing_zeros() as usize;",
        "let base = word.checked_mul(64)?;",
        "let bin = base.checked_add(offset)?;",
        "return Some(bin);",
        "word = word.checked_add(1)?;",
        "while word < nonempty.len() {",
        "let bitmap: u64 = nonempty[word];",
        "if bitmap != 0 {",
        "let offset: usize = bitmap.trailing_zeros() as usize;",
        "return Some(bin);",
        "word = word.checked_add(1)?;",
        "None",
    ];
    let mut position = 0;
    if required.iter().all(|expected| {
        if let Some(offset) = body[position..].iter().position(|line| line == expected) {
            position += offset + 1;
            true
        } else {
            false
        }
    }) {
        vec![TlsfFindNonemptyBinModel {
            name: "tlsf_find_nonempty_bin".to_owned(),
            refines: target.trim().to_owned(),
        }]
    } else {
        Vec::new()
    }
}

fn parse_tlsf_take_candidate_models(source: &str) -> Vec<TlsfTakeCandidateModel> {
    let lines = source.lines().collect::<Vec<_>>();
    let Some(index) = lines
        .iter()
        .position(|line| line.trim().starts_with("fn tlsf_take_candidate("))
    else {
        return Vec::new();
    };
    let Some(target) = index
        .checked_sub(1)
        .and_then(|i| lines.get(i))
        .and_then(|line| line.trim().strip_prefix("// refines "))
    else {
        return Vec::new();
    };
    let body = lines[index + 1..]
        .iter()
        .map(|line| line.trim())
        .collect::<Vec<_>>();
    let required = [
        "let bin: usize = tlsf_find_nonempty_bin(nonempty, start_bin)?;",
        "if bin >= heads.len() { return None; }",
        "let word: usize = bin >> 6;",
        "let bit: usize = bin & 63;",
        "if word >= nonempty.len() { return None; }",
        "let block: usize = heads[bin];",
        "if block >= next.len() { return None; }",
        "if block >= previous.len() { return None; }",
        "let successor: usize = next[block];",
        "tlsf_remove(heads, next, previous, bin, block)?;",
        "if successor >= next.len() {",
        "let bitmap: u64 = nonempty[word];",
        "let bit_mask: u64 = 1 << bit;",
        "nonempty[word] = bitmap & !bit_mask;",
        "Some(block)",
    ];
    let mut position = 0;
    if required.iter().all(|expected| {
        if let Some(offset) = body[position..].iter().position(|line| line == expected) {
            position += offset + 1;
            true
        } else {
            false
        }
    }) {
        vec![TlsfTakeCandidateModel {
            name: "tlsf_take_candidate".to_owned(),
            refines: target.trim().to_owned(),
        }]
    } else {
        Vec::new()
    }
}

fn parse_tlsf_find_nonempty_class_models(source: &str) -> Vec<TlsfFindNonemptyClassModel> {
    let lines = source.lines().collect::<Vec<_>>();
    let Some(index) = lines
        .iter()
        .position(|line| line.trim().starts_with("fn tlsf_find_nonempty_class("))
    else {
        return Vec::new();
    };
    let Some(target) = index
        .checked_sub(1)
        .and_then(|i| lines.get(i))
        .and_then(|line| line.trim().strip_prefix("// refines "))
    else {
        return Vec::new();
    };
    let body = lines[index + 1..]
        .iter()
        .map(|line| line.trim())
        .collect::<Vec<_>>();
    let required = [
        "if start_fl >= second_nonempty.len() { return None; }",
        "if start_sl >= 32 { return None; }",
        "let second_bitmap: u32 = second_nonempty[start_fl];",
        "let second_masked: u32 = second_bitmap & (u32::MAX << start_sl);",
        "if second_masked != 0 {",
        "let found_sl: usize = second_masked.trailing_zeros() as usize;",
        "return Some(bin);",
        "let next_fl: usize = start_fl.checked_add(1)?;",
        "let first_bitmap: u64 = first_nonempty[0];",
        "let first_masked: u64 = first_bitmap & (u64::MAX << next_fl);",
        "if first_masked == 0 { return None; }",
        "let found_fl: usize = first_masked.trailing_zeros() as usize;",
        "let found_second: u32 = second_nonempty[found_fl];",
        "if found_second == 0 { return None; }",
        "let found_sl: usize = found_second.trailing_zeros() as usize;",
        "Some(bin)",
    ];
    let mut position = 0;
    if required.iter().all(|expected| {
        if let Some(offset) = body[position..].iter().position(|line| line == expected) {
            position += offset + 1;
            true
        } else {
            false
        }
    }) {
        vec![TlsfFindNonemptyClassModel {
            name: "tlsf_find_nonempty_class".to_owned(),
            refines: target.trim().to_owned(),
        }]
    } else {
        Vec::new()
    }
}

fn parse_tlsf_take_candidate_class_models(source: &str) -> Vec<TlsfTakeCandidateModel> {
    let lines = source.lines().collect::<Vec<_>>();
    let Some(index) = lines
        .iter()
        .position(|line| line.trim().starts_with("fn tlsf_take_candidate_class("))
    else {
        return Vec::new();
    };
    let Some(target) = index
        .checked_sub(1)
        .and_then(|i| lines.get(i))
        .and_then(|line| line.trim().strip_prefix("// refines "))
    else {
        return Vec::new();
    };
    let body = lines[index + 1..]
        .iter()
        .map(|line| line.trim())
        .collect::<Vec<_>>();
    let required = [
        "let bin: usize = tlsf_find_nonempty_class(second_nonempty, first_nonempty, start_fl, start_sl)?;",
        "if bin >= heads.len() { return None; }",
        "let found_fl: usize = bin >> 5;",
        "let found_sl: usize = bin & 31;",
        "if found_fl >= second_nonempty.len() { return None; }",
        "let block: usize = heads[bin];",
        "if block >= next.len() { return None; }",
        "if block >= previous.len() { return None; }",
        "let successor: usize = next[block];",
        "tlsf_remove(heads, next, previous, bin, block)?;",
        "if successor >= next.len() {",
        "let old_second: u32 = second_nonempty[found_fl];",
        "let second_mask: u32 = 1 << found_sl;",
        "let new_second: u32 = old_second & !second_mask;",
        "second_nonempty[found_fl] = new_second;",
        "if new_second == 0 {",
        "let old_first: u64 = first_nonempty[0];",
        "let first_mask: u64 = 1 << found_fl;",
        "first_nonempty[0] = old_first & !first_mask;",
        "Some(block)",
    ];
    let mut position = 0;
    if required.iter().all(|expected| {
        if let Some(offset) = body[position..].iter().position(|line| line == expected) {
            position += offset + 1;
            true
        } else {
            false
        }
    }) {
        vec![TlsfTakeCandidateModel {
            name: "tlsf_take_candidate_class".to_owned(),
            refines: target.trim().to_owned(),
        }]
    } else {
        Vec::new()
    }
}

fn parse_tlsf_mark_free_models(source: &str) -> Vec<TlsfMarkFreeModel> {
    let lines = source.lines().collect::<Vec<_>>();
    let Some(index) = lines
        .iter()
        .position(|line| line.trim().starts_with("fn tlsf_mark_free("))
    else {
        return Vec::new();
    };
    let Some(target) = index
        .checked_sub(1)
        .and_then(|i| lines.get(i))
        .and_then(|line| line.trim().strip_prefix("// refines "))
    else {
        return Vec::new();
    };
    let body = lines[index + 1..]
        .iter()
        .map(|line| line.trim())
        .collect::<Vec<_>>();
    let required = [
        "if block >= offsets.len() { return None; }",
        "if block >= sizes.len() { return None; }",
        "if block >= is_free.len() { return None; }",
        "if block >= prev_free.len() { return None; }",
        "if is_free[block] != 0 { return None; }",
        "if offsets[block] != returned_offset { return None; }",
        "if sizes[block] != returned_bytes { return None; }",
        "if block == usize::MAX { return None; }",
        "let successor: usize = block + 1;",
        "is_free[block] = 1;",
        "if successor < prev_free.len() {",
        "prev_free[successor] = 1;",
        "Some(())",
    ];
    let mut position = 0;
    if required.iter().all(|expected| {
        if let Some(offset) = body[position..].iter().position(|line| line == expected) {
            position += offset + 1;
            true
        } else {
            false
        }
    }) {
        vec![TlsfMarkFreeModel {
            name: "tlsf_mark_free".to_owned(),
            refines: target.trim().to_owned(),
        }]
    } else {
        Vec::new()
    }
}

fn parse_tlsf_classify_size_models(source: &str) -> Vec<TlsfClassifySizeModel> {
    let lines = source.lines().collect::<Vec<_>>();
    let Some(index) = lines
        .iter()
        .position(|line| line.trim().starts_with("fn tlsf_classify_size("))
    else {
        return Vec::new();
    };
    let Some(target) = index
        .checked_sub(1)
        .and_then(|i| lines.get(i))
        .and_then(|line| line.trim().strip_prefix("// refines "))
    else {
        return Vec::new();
    };
    let body = lines[index + 1..]
        .iter()
        .map(|line| line.trim())
        .collect::<Vec<_>>();
    let required = [
        "if size == 0 { return None; }",
        "if size <= 256 {",
        "let predecessor: usize = size - 1;",
        "let sl: usize = predecessor >> 3;",
        "return Some(sl);",
        "let leading: usize = size.leading_zeros() as usize;",
        "let fl: usize = 63 - leading;",
        "let base: usize = 1 << fl;",
        "if base > size { return None; }",
        "let shift: usize = fl - 5;",
        "let step: usize = 1 << shift;",
        "let delta: usize = size - base;",
        "let sl: usize = delta / step;",
        "if sl >= 32 { return None; }",
        "let encoded_base: usize = fl.checked_mul(32)?;",
        "let encoded: usize = encoded_base.checked_add(sl)?;",
        "Some(encoded)",
    ];
    let mut position = 0;
    if required.iter().all(|expected| {
        if let Some(offset) = body[position..].iter().position(|line| line == expected) {
            position += offset + 1;
            true
        } else {
            false
        }
    }) {
        vec![TlsfClassifySizeModel {
            name: "tlsf_classify_size".to_owned(),
            refines: target.trim().to_owned(),
        }]
    } else {
        Vec::new()
    }
}

fn parse_tlsf_insert_class_models(source: &str) -> Vec<TlsfInsertClassModel> {
    let lines = source.lines().collect::<Vec<_>>();
    let Some(index) = lines
        .iter()
        .position(|line| line.trim().starts_with("fn tlsf_insert_class("))
    else {
        return Vec::new();
    };
    let Some(target) = index
        .checked_sub(1)
        .and_then(|i| lines.get(i))
        .and_then(|line| line.trim().strip_prefix("// refines "))
    else {
        return Vec::new();
    };
    let body = lines[index + 1..]
        .iter()
        .map(|line| line.trim())
        .collect::<Vec<_>>();
    let required = [
        "if bin >= heads.len() { return None; }",
        "let fl: usize = bin >> 5;",
        "let sl: usize = bin & 31;",
        "if fl >= second_nonempty.len() { return None; }",
        "if first_nonempty.len() == 0 { return None; }",
        "if block >= next.len() { return None; }",
        "if block >= previous.len() { return None; }",
        "tlsf_insert(heads, next, previous, bin, block)?;",
        "let second_mask: u32 = 1 << sl;",
        "second_nonempty[fl] = second_nonempty[fl] | second_mask;",
        "let first_mask: u64 = 1 << fl;",
        "first_nonempty[0] = first_nonempty[0] | first_mask;",
        "Some(())",
    ];
    let mut position = 0;
    if required.iter().all(|expected| {
        if let Some(offset) = body[position..].iter().position(|line| line == expected) {
            position += offset + 1;
            true
        } else {
            false
        }
    }) {
        vec![TlsfInsertClassModel {
            name: "tlsf_insert_class".to_owned(),
            refines: target.trim().to_owned(),
        }]
    } else {
        Vec::new()
    }
}

fn parse_tlsf_remove_class_models(source: &str) -> Vec<TlsfInsertClassModel> {
    let lines = source.lines().collect::<Vec<_>>();
    let Some(index) = lines
        .iter()
        .position(|line| line.trim().starts_with("fn tlsf_remove_class("))
    else {
        return Vec::new();
    };
    let Some(target) = index
        .checked_sub(1)
        .and_then(|i| lines.get(i))
        .and_then(|line| line.trim().strip_prefix("// refines "))
    else {
        return Vec::new();
    };
    let body = lines[index + 1..]
        .iter()
        .map(|line| line.trim())
        .collect::<Vec<_>>();
    let required = [
        "if bin >= heads.len() { return None; }",
        "let fl: usize = bin >> 5;",
        "let sl: usize = bin & 31;",
        "if fl >= second_nonempty.len() { return None; }",
        "if first_nonempty.len() == 0 { return None; }",
        "if block >= next.len() { return None; }",
        "if block >= previous.len() { return None; }",
        "let successor: usize = next[block];",
        "let predecessor: usize = previous[block];",
        "tlsf_remove(heads, next, previous, bin, block)?;",
        "if predecessor >= next.len() && successor >= next.len() {",
        "let old_second: u32 = second_nonempty[fl];",
        "let second_mask: u32 = 1 << sl;",
        "let new_second: u32 = old_second & !second_mask;",
        "second_nonempty[fl] = new_second;",
        "if new_second == 0 {",
        "let old_first: u64 = first_nonempty[0];",
        "let first_mask: u64 = 1 << fl;",
        "first_nonempty[0] = old_first & !first_mask;",
        "Some(())",
    ];
    let mut position = 0;
    if required.iter().all(|expected| {
        if let Some(offset) = body[position..].iter().position(|line| line == expected) {
            position += offset + 1;
            true
        } else {
            false
        }
    }) {
        vec![TlsfInsertClassModel {
            name: "tlsf_remove_class".to_owned(),
            refines: target.trim().to_owned(),
        }]
    } else {
        Vec::new()
    }
}

fn parse_tlsf_deallocate_uncoalesced_models(source: &str) -> Vec<TlsfDeallocateUncoalescedModel> {
    let lines = source.lines().collect::<Vec<_>>();
    let Some(index) = lines
        .iter()
        .position(|line| line.trim().starts_with("fn tlsf_deallocate_uncoalesced("))
    else {
        return Vec::new();
    };
    let Some(target) = index
        .checked_sub(1)
        .and_then(|i| lines.get(i))
        .and_then(|line| line.trim().strip_prefix("// refines "))
    else {
        return Vec::new();
    };
    let body = lines[index + 1..]
        .iter()
        .map(|line| line.trim())
        .collect::<Vec<_>>();
    let required = [
        "if block_count > offsets.len() { return None; }",
        "if block_count > sizes.len() { return None; }",
        "if block_count > is_free.len() { return None; }",
        "if block_count > prev_free.len() { return None; }",
        "if block >= block_count { return None; }",
        "if block >= offsets.len() { return None; }",
        "if sizes[block] != returned_bytes { return None; }",
        "let bin: usize = tlsf_classify_size(returned_bytes)?;",
        "if bin >= heads.len() { return None; }",
        "if returned_offset >= previous.len() { return None; }",
        "tlsf_mark_free(offsets, sizes, is_free, prev_free, block, returned_offset, returned_bytes)?;",
        "tlsf_insert_class(second_nonempty, first_nonempty, heads, next, previous, bin, returned_offset)?;",
        "Some(())",
    ];
    let mut position = 0;
    if required.iter().all(|expected| {
        if let Some(offset) = body[position..].iter().position(|line| line == expected) {
            position += offset + 1;
            true
        } else {
            false
        }
    }) {
        vec![TlsfDeallocateUncoalescedModel {
            name: "tlsf_deallocate_uncoalesced".to_owned(),
            refines: target.trim().to_owned(),
        }]
    } else {
        Vec::new()
    }
}

fn parse_tlsf_coalesce_physical_models(source: &str) -> Vec<TlsfCoalescePhysicalModel> {
    let lines = source.lines().collect::<Vec<_>>();
    let Some(index) = lines
        .iter()
        .position(|line| line.trim().starts_with("fn tlsf_coalesce_physical("))
    else {
        return Vec::new();
    };
    let Some(target) = index
        .checked_sub(1)
        .and_then(|i| lines.get(i))
        .and_then(|line| line.trim().strip_prefix("// refines "))
    else {
        return Vec::new();
    };
    let body = lines[index + 1..]
        .iter()
        .map(|line| line.trim())
        .collect::<Vec<_>>();
    let required = [
        "if block_count > offsets.len() { return None; }",
        "if left == usize::MAX { return None; }",
        "let right: usize = left + 1;",
        "if right >= block_count { return None; }",
        "if is_free[left] == 0 { return None; }",
        "if is_free[right] == 0 { return None; }",
        "let left_end: usize = offsets[left].checked_add(sizes[left])?;",
        "if left_end != offsets[right] { return None; }",
        "let merged_size: usize = sizes[left].checked_add(sizes[right])?;",
        "sizes[left] = merged_size;",
        "while cursor < block_count - 1 {",
        "offsets[cursor] = offsets[source];",
        "prev_free[cursor] = prev_free[source];",
        "Some(block_count - 1)",
    ];
    let mut position = 0;
    if required.iter().all(|expected| {
        if let Some(offset) = body[position..].iter().position(|line| line == expected) {
            position += offset + 1;
            true
        } else {
            false
        }
    }) {
        vec![TlsfCoalescePhysicalModel {
            name: "tlsf_coalesce_physical".to_owned(),
            refines: target.trim().to_owned(),
        }]
    } else {
        Vec::new()
    }
}

fn parse_tlsf_coalesce_class_models(source: &str) -> Vec<TlsfCoalescePhysicalModel> {
    let lines = source.lines().collect::<Vec<_>>();
    let Some(index) = lines
        .iter()
        .position(|line| line.trim().starts_with("fn tlsf_coalesce_class("))
    else {
        return Vec::new();
    };
    let Some(target) = index
        .checked_sub(1)
        .and_then(|i| lines.get(i))
        .and_then(|line| line.trim().strip_prefix("// refines "))
    else {
        return Vec::new();
    };
    let body = lines[index + 1..]
        .iter()
        .map(|line| line.trim())
        .collect::<Vec<_>>();
    let required = [
        "if block_count > offsets.len() { return None; }",
        "if left == usize::MAX { return None; }",
        "let right: usize = left + 1;",
        "if right >= block_count { return None; }",
        "if is_free[left] == 0 { return None; }",
        "if is_free[right] == 0 { return None; }",
        "let left_offset: usize = offsets[left];",
        "let right_offset: usize = offsets[right];",
        "let left_size: usize = sizes[left];",
        "let right_size: usize = sizes[right];",
        "let left_end: usize = left_offset.checked_add(left_size)?;",
        "if left_end != right_offset { return None; }",
        "let merged_size: usize = left_size.checked_add(right_size)?;",
        "let left_bin: usize = tlsf_classify_size(left_size)?;",
        "let right_bin: usize = tlsf_classify_size(right_size)?;",
        "let merged_bin: usize = tlsf_classify_size(merged_size)?;",
        "if left_bin >= heads.len() { return None; }",
        "if left_fl >= second_nonempty.len() { return None; }",
        "if first_nonempty.len() == 0 { return None; }",
        "if left_offset >= next.len() { return None; }",
        "if right_offset >= previous.len() { return None; }",
        "tlsf_remove_class(second_nonempty, first_nonempty, heads, next, previous, left_bin, left_offset)?;",
        "tlsf_remove_class(second_nonempty, first_nonempty, heads, next, previous, right_bin, right_offset)?;",
        "let new_count: usize = tlsf_coalesce_physical(offsets, sizes, is_free, prev_free, block_count, left)?;",
        "tlsf_insert_class(second_nonempty, first_nonempty, heads, next, previous, merged_bin, left_offset)?;",
        "Some(new_count)",
    ];
    let mut position = 0;
    if required.iter().all(|expected| {
        if let Some(offset) = body[position..].iter().position(|line| line == expected) {
            position += offset + 1;
            true
        } else {
            false
        }
    }) {
        vec![TlsfCoalescePhysicalModel {
            name: "tlsf_coalesce_class".to_owned(),
            refines: target.trim().to_owned(),
        }]
    } else {
        Vec::new()
    }
}

fn parse_tlsf_coalesce_if_possible_models(source: &str) -> Vec<TlsfCoalescePhysicalModel> {
    let lines = source.lines().collect::<Vec<_>>();
    let Some(index) = lines
        .iter()
        .position(|line| line.trim().starts_with("fn tlsf_coalesce_if_possible("))
    else {
        return Vec::new();
    };
    let Some(target) = index
        .checked_sub(1)
        .and_then(|i| lines.get(i))
        .and_then(|line| line.trim().strip_prefix("// refines "))
    else {
        return Vec::new();
    };
    let body = lines[index + 1..]
        .iter()
        .map(|line| line.trim())
        .collect::<Vec<_>>();
    let required = [
        "if block_count > offsets.len() { return None; }",
        "if block_count > prev_free.len() { return None; }",
        "if left == usize::MAX { return Some(block_count); }",
        "let right: usize = left + 1;",
        "if right >= block_count { return Some(block_count); }",
        "if is_free[left] == 0 { return Some(block_count); }",
        "if is_free[right] == 0 { return Some(block_count); }",
        "let left_end: usize = offsets[left].checked_add(sizes[left])?;",
        "if left_end != offsets[right] { return Some(block_count); }",
        "tlsf_coalesce_class(offsets, sizes, is_free, prev_free, second_nonempty, first_nonempty, heads, next, previous, block_count, left)",
    ];
    let mut position = 0;
    if required.iter().all(|expected| {
        if let Some(offset) = body[position..].iter().position(|line| line == expected) {
            position += offset + 1;
            true
        } else {
            false
        }
    }) {
        vec![TlsfCoalescePhysicalModel {
            name: "tlsf_coalesce_if_possible".to_owned(),
            refines: target.trim().to_owned(),
        }]
    } else {
        Vec::new()
    }
}

fn parse_tlsf_deallocate_models(source: &str) -> Vec<TlsfCoalescePhysicalModel> {
    let lines = source.lines().collect::<Vec<_>>();
    let Some(index) = lines
        .iter()
        .position(|line| line.trim().starts_with("fn tlsf_deallocate("))
    else {
        return Vec::new();
    };
    let Some(target) = index
        .checked_sub(1)
        .and_then(|i| lines.get(i))
        .and_then(|line| line.trim().strip_prefix("// refines "))
    else {
        return Vec::new();
    };
    let body = lines[index + 1..]
        .iter()
        .map(|line| line.trim())
        .collect::<Vec<_>>();
    let required = [
        "tlsf_deallocate_uncoalesced(offsets, sizes, is_free, prev_free, second_nonempty, first_nonempty, heads, next, previous, block_count, block, returned_offset, returned_bytes)?;",
        "let after_right: usize = tlsf_coalesce_if_possible(offsets, sizes, is_free, prev_free, second_nonempty, first_nonempty, heads, next, previous, block_count, block)?;",
        "if block == 0 { return Some(after_right); }",
        "let left: usize = block - 1;",
        "tlsf_coalesce_if_possible(offsets, sizes, is_free, prev_free, second_nonempty, first_nonempty, heads, next, previous, after_right, left)",
    ];
    let mut position = 0;
    if required.iter().all(|expected| {
        if let Some(offset) = body[position..].iter().position(|line| line == expected) {
            position += offset + 1;
            true
        } else {
            false
        }
    }) {
        vec![TlsfCoalescePhysicalModel {
            name: "tlsf_deallocate".to_owned(),
            refines: target.trim().to_owned(),
        }]
    } else {
        Vec::new()
    }
}

fn logical_lines(source: &str) -> Result<Vec<(usize, String)>, String> {
    let lines: Vec<&str> = source.lines().collect();
    let mut result = Vec::new();
    let mut i = 0;
    while i < lines.len() {
        let trimmed = lines[i].trim();
        if trimmed.starts_with("proof ") && trimmed.contains(" by {") {
            let start = i + 1;
            let mut declaration = trimmed.replace(" by {", " by ");
            i += 1;
            let mut closed = false;
            while i < lines.len() {
                let body = lines[i].trim();
                if body == "}" || body == "};" {
                    closed = true;
                    break;
                }
                declaration.push(' ');
                declaration.push_str(body.trim_end_matches(';'));
                i += 1;
            }
            if !closed {
                return Err(format!("line {start}: unclosed proof block"));
            }
            declaration.push(';');
            result.push((start, declaration));
        } else {
            result.push((i + 1, lines[i].to_owned()));
        }
        i += 1;
    }
    Ok(result)
}

fn usize_let(line: &str) -> Option<(&str, &str)> {
    let rest = line.strip_prefix("let ")?;
    let (name, rest) = rest.split_once(':')?;
    let rest = rest.trim_start().strip_prefix("usize")?.trim_start();
    let expression = rest.strip_prefix('=')?.trim().strip_suffix(';')?.trim();
    Some((name.trim().trim_start_matches("mut "), expression))
}

fn arithmetic_expression(expr: &str) -> bool {
    expr.contains('+') || expr.contains('*') || expr.contains('-')
}

fn overflow_obligation(expr: &str) -> Result<String, String> {
    let lean = to_lean_expr(expr);
    if let Some((lhs, rhs)) = lean.split_once('-') {
        Ok(format!("{} ≤ {}", rhs.trim(), lhs.trim()))
    } else if lean.contains('+') || lean.contains('*') {
        Ok(format!("({lean}) ≤ usize_max"))
    } else {
        Err(format!("unsupported arithmetic expression `{expr}`"))
    }
}

fn proof_facts(vars: &[String], cfg_facts: &[String]) -> Vec<String> {
    vars.iter()
        .map(|var| format!("{} ≤ usize_max", lean_ident(var)))
        .chain(cfg_facts.iter().cloned())
        .collect()
}

fn proof_header(vars: &[String]) -> String {
    if vars.is_empty() {
        " (usize_max : Nat)".to_owned()
    } else {
        format!(
            " (usize_max {} : Nat)",
            vars.iter()
                .map(|var| lean_ident(var))
                .collect::<Vec<_>>()
                .join(" ")
        )
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
    let expr = expr.replace("usize::MAX", "usize_max");
    if expr.contains("::") || expr.contains('&') || expr.contains('|') {
        return false;
    }
    let lean = to_lean_expr(&expr);
    lean.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .filter(|word| !word.is_empty() && !word.bytes().all(|b| b.is_ascii_digit()))
        .all(|word| word == "usize_max" || nat_vars.iter().any(|var| lean_ident(var) == word))
}

fn to_lean_expr(expr: &str) -> String {
    let mut rewritten = expr.replace("usize::MAX", "usize_max");
    while let Some(pos) = rewritten.find(".len()") {
        let start = rewritten[..pos]
            .rfind(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .map_or(0, |i| i + 1);
        let name = rewritten[start..pos].to_owned();
        rewritten.replace_range(start..pos + 6, &format!("{name}_len"));
    }
    let rewritten = rewritten
        .replace(">=", "≥")
        .replace("<=", "≤")
        .replace("==", "=")
        .replace("!=", "≠")
        .replace("&&", "∧")
        .replace("||", "∨");
    rewrite_lean_identifiers(&rewritten)
}

fn lean_ident(name: &str) -> String {
    match name {
        "end" | "match" | "theorem" | "namespace" => format!("{name}_"),
        _ => name.to_owned(),
    }
}

fn rewrite_lean_identifiers(expr: &str) -> String {
    let mut out = String::new();
    let mut token = String::new();
    for ch in expr.chars().chain(std::iter::once(' ')) {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            token.push(ch);
        } else {
            if !token.is_empty() {
                out.push_str(&lean_ident(&token));
                token.clear();
            }
            if ch != ' ' || !expr.ends_with(' ') || out.len() < expr.len() {
                out.push(ch);
            }
        }
    }
    out.trim_end().to_owned()
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
            let access = if mutable {
                format!("(*unsafe {{ {array}.get_unchecked_mut({rust_subscript}) }})")
            } else {
                format!("unsafe {{ *{array}.get_unchecked({rust_subscript}) }}")
            };
            out.push_str(&access);
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
        let expected = to_lean_expr(&obligation(a));
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
    let mut out = String::from("import Init.Omega\n");
    if module
        .scalar_models
        .iter()
        .any(|model| model.refines.is_some())
        || module
            .array_models
            .iter()
            .any(|model| model.refines.is_some())
        || module
            .read_models
            .iter()
            .any(|model| model.refines.is_some())
        || module
            .copy_models
            .iter()
            .any(|model| model.refines.is_some())
    {
        out.push_str("import Luffs.Runtime.Containers\n");
    }
    if !module.tlsf_insert_models.is_empty()
        || !module.tlsf_remove_models.is_empty()
        || !module.tlsf_find_fit_models.is_empty()
        || !module.tlsf_find_nonempty_bin_models.is_empty()
        || !module.tlsf_take_candidate_models.is_empty()
        || !module.tlsf_find_nonempty_class_models.is_empty()
        || !module.tlsf_take_candidate_class_models.is_empty()
        || !module.tlsf_mark_free_models.is_empty()
        || !module.tlsf_classify_size_models.is_empty()
        || !module.tlsf_insert_class_models.is_empty()
        || !module.tlsf_remove_class_models.is_empty()
        || !module.tlsf_deallocate_uncoalesced_models.is_empty()
        || !module.tlsf_coalesce_physical_models.is_empty()
        || !module.tlsf_coalesce_class_models.is_empty()
    {
        out.push_str("import Luffs.Runtime.TLSF\n");
    }
    out.push_str(
        "\nset_option autoImplicit false\nset_option linter.unusedVariables false\n\nnamespace LuffsGenerated\n\n",
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
    for model in &module.scalar_models {
        out.push_str("def ");
        out.push_str(&model.name);
        out.push_str("_model");
        if !model.params.is_empty() {
            out.push_str(" (");
            out.push_str(&model.params.join(" "));
            out.push_str(" : Nat)");
        }
        out.push_str(" : Option Nat :=\n  ");
        for guard in &model.guards {
            out.push_str("if ");
            out.push_str(guard);
            out.push_str(" then none else\n  ");
        }
        for (name, expression) in &model.lets {
            out.push_str("let ");
            out.push_str(name);
            out.push_str(" := ");
            out.push_str(expression);
            out.push_str("\n  ");
        }
        out.push_str("some (");
        out.push_str(&model.result);
        out.push_str(")\n\n");
        if let Some(target) = &model.refines {
            out.push_str("theorem ");
            out.push_str(&model.name);
            out.push_str("_refines : ");
            out.push_str(&model.name);
            out.push_str("_model = ");
            out.push_str(target);
            out.push_str(" := by\n  funext ");
            out.push_str(&model.params.join(" "));
            out.push_str("\n  simp [");
            out.push_str(&model.name);
            out.push_str("_model, ");
            out.push_str(target);
            out.push_str(", Nat.pos_iff_ne_zero]\n\n");
        }
    }
    for model in &module.array_models {
        out.push_str("def ");
        out.push_str(&model.name);
        out.push_str("_model");
        for (name, ty) in &model.params {
            out.push_str(" (");
            out.push_str(name);
            out.push_str(" : ");
            out.push_str(ty);
            out.push(')');
        }
        if model.returns_unit {
            out.push_str(" : Option (List (Fin 256)) :=\n  ");
        } else {
            out.push_str(" : Option (List (Fin 256) × Nat) :=\n  ");
        }
        for guard in &model.guards {
            out.push_str("if ");
            out.push_str(guard);
            out.push_str(" then none else\n  ");
        }
        for (name, expression) in &model.lets {
            out.push_str("let ");
            out.push_str(name);
            out.push_str(" := ");
            out.push_str(expression);
            out.push_str("\n  ");
        }
        out.push_str("let ");
        out.push_str(&model.array);
        out.push_str(" := ");
        out.push_str(&model.array);
        out.push_str(".set ");
        out.push_str(&model.assignment.0);
        out.push(' ');
        out.push_str(&model.assignment.1);
        out.push_str("\n  some (");
        out.push_str(&model.array);
        if !model.returns_unit {
            out.push_str(", ");
            out.push_str(&model.result);
        }
        out.push_str(")\n\n");
        if let Some(target) = &model.refines {
            out.push_str("theorem ");
            out.push_str(&model.name);
            out.push_str("_refines : ");
            out.push_str(&model.name);
            out.push_str("_model = ");
            out.push_str(target);
            out.push_str(" := by\n  funext ");
            out.push_str(
                &model
                    .params
                    .iter()
                    .map(|(name, _)| name.as_str())
                    .collect::<Vec<_>>()
                    .join(" "),
            );
            out.push_str("\n  simp [");
            out.push_str(&model.name);
            out.push_str("_model, ");
            out.push_str(target);
            out.push_str("]\n\n");
        }
    }
    for model in &module.read_models {
        out.push_str("def ");
        out.push_str(&model.name);
        out.push_str("_model");
        for (name, ty) in &model.params {
            out.push_str(&format!(" ({name} : {ty})"));
        }
        out.push_str(" : Option (");
        out.push_str(&model.result_type);
        out.push_str(") :=\n  ");
        for guard in &model.guards {
            out.push_str(&format!("if {guard} then none else\n  "));
        }
        for (name, expression) in &model.lets {
            out.push_str(&format!("let {name} := {expression}\n  "));
        }
        out.push_str(&model.result);
        out.push_str("\n\n");
        if let Some(target) = &model.refines {
            out.push_str(&format!(
                "theorem {}_refines : {}_model = {} := by\n  funext {}\n  simp [{}, {}]\n\n",
                model.name,
                model.name,
                target,
                model
                    .params
                    .iter()
                    .map(|(name, _)| name.as_str())
                    .collect::<Vec<_>>()
                    .join(" "),
                format!("{}_model", model.name),
                target
            ));
        }
    }
    for model in &module.copy_models {
        out.push_str(&format!(
            "def {}_model ({} : List (Fin 256)) ({} : List (Fin 256)) ({} : Nat) : Option (List (Fin 256)) :=\n  ",
            model.name, model.source, model.destination, model.len
        ));
        for guard in &model.guards {
            out.push_str(&format!("if {guard} then none else\n  "));
        }
        out.push_str(&format!(
            "some ({}.take {} ++ {}.drop {})\n\n",
            model.source, model.len, model.destination, model.len
        ));
        if let Some(target) = &model.refines {
            out.push_str(&format!(
                "theorem {}_refines : {}_model = {} := by\n  funext {} {} {}\n  simp [{}_model, {}]\n\n",
                model.name,
                model.name,
                target,
                model.source,
                model.destination,
                model.len,
                model.name,
                target
            ));
        }
    }
    for model in &module.tlsf_insert_models {
        out.push_str(&format!(
            "def {}_model (heads next previous : List Nat) (bin block : Nat) : Option (List Nat × List Nat × List Nat) :=\n  \
if bin ≥ heads.length then none else\n  \
if block ≥ next.length then none else\n  \
if block ≥ previous.length then none else\n  \
let old_head := heads[bin]?.getD 0\n  \
let next := next.set block old_head\n  \
let previous := previous.set block next.length\n  \
let previous := if old_head < previous.length then previous.set old_head block else previous\n  \
let heads := heads.set bin block\n  \
some (heads, next, previous)\n\n",
            model.name
        ));
        out.push_str(&format!(
            "theorem {}_refines : {}_model = {} := by\n  funext heads next previous bin block\n  \
by_cases hbin : bin ≥ heads.length <;>\n  \
by_cases hnext : block ≥ next.length <;>\n  \
by_cases hprevious : block ≥ previous.length <;>\n  \
simp [{}_model, {}, Luffs.Runtime.TLSF.insertArrays, Luffs.Runtime.TLSF.insert,\n    \
hbin, hnext, hprevious]\n\n",
            model.name, model.name, model.refines, model.name, model.refines
        ));
    }
    for model in &module.tlsf_remove_models {
        out.push_str(&format!(
            "def {}_model (heads next previous : List Nat) (bin block : Nat) : Option (List Nat × List Nat × List Nat) :=\n  \
if bin ≥ heads.length then none else\n  \
if block ≥ next.length then none else\n  \
if block ≥ previous.length then none else\n  \
let successor := next[block]?.getD next.length\n  \
let predecessor := previous[block]?.getD next.length\n  \
let heads := if predecessor ≥ next.length then heads.set bin successor else heads\n  \
let next := if predecessor < next.length then next.set predecessor successor else next\n  \
let previous := if successor < previous.length then previous.set successor predecessor else previous\n  \
let next := next.set block next.length\n  \
let previous := previous.set block previous.length\n  \
some (heads, next, previous)\n\n",
            model.name
        ));
        out.push_str(&format!(
            "theorem {}_refines : {}_model = {} := by\n  funext heads next previous bin block\n  \
by_cases hbin : bin ≥ heads.length <;>\n  \
by_cases hnext : block ≥ next.length <;>\n  \
by_cases hprevious : block ≥ previous.length <;>\n  \
simp [{}_model, {}, Luffs.Runtime.TLSF.removeArrays, Luffs.Runtime.TLSF.remove,\n    \
hbin, hnext, hprevious] <;>\n  \
split <;> simp_all <;> split <;> simp_all\n\n",
            model.name, model.name, model.refines, model.name, model.refines
        ));
    }
    for model in &module.tlsf_find_fit_models {
        out.push_str(&format!(
            "def {}_model (sizes : List Nat) (flags : List (Fin 256)) (request : Nat) : Option Nat :=\n  \
match sizes, flags with\n  \
| size :: more_sizes, flag :: more_flags =>\n      \
if flag.val ≠ 0 ∧ request ≤ size then some 0\n      \
else ({}_model more_sizes more_flags request).map Nat.succ\n  \
| _, _ => none\ntermination_by sizes.length\n\n",
            model.name, model.name
        ));
        out.push_str(&format!(
            "theorem {}_refines : {}_model = {} := by\n  funext sizes flags request\n  \
induction sizes generalizing flags with\n  \
| nil => cases flags <;> simp only [{}_model, {}]\n  \
| cons size more_sizes ih =>\n    cases flags with\n    \
| nil => simp only [{}_model, {}]\n    \
| cons flag more_flags => simp only [{}_model, {}, ih]\n\n",
            model.name,
            model.name,
            model.refines,
            model.name,
            model.refines,
            model.name,
            model.refines,
            model.name,
            model.refines
        ));
    }
    for model in &module.tlsf_find_nonempty_bin_models {
        out.push_str(&format!(
            "def {}_model (words : List (BitVec 64)) (start : Nat) : Option Nat :=\n  \
Luffs.Runtime.TLSF.findNonemptyBinLowered words start\n\n",
            model.name
        ));
        out.push_str(&format!(
            "theorem {}_refines : {}_model = {} := by\n  \
funext words start\n  \
exact Luffs.Runtime.TLSF.findNonemptyBinLowered_refines words start\n\n",
            model.name, model.name, model.refines
        ));
    }
    for model in &module.tlsf_take_candidate_models {
        out.push_str(&format!(
            "def {}_model (words : List (BitVec 64)) (heads next previous : List Nat) (start : Nat) : Option Luffs.Runtime.TLSF.CandidateResult :=\n  \
{} words heads next previous start\n\n",
            model.name, model.refines
        ));
        out.push_str(&format!(
            "theorem {}_refines : {}_model = {} := by rfl\n\n",
            model.name, model.name, model.refines
        ));
    }
    for model in &module.tlsf_find_nonempty_class_models {
        out.push_str(&format!(
            "def {}_model (second : List (BitVec 32)) (first : BitVec 64) (start_fl start_sl : Nat) : Option Nat :=\n  \
Luffs.Runtime.TLSF.findNonemptyClassLowered second first start_fl start_sl\n\n",
            model.name
        ));
        out.push_str(&format!(
            "theorem {}_refines (second : List (BitVec 32)) (first : BitVec 64)\n    \
(hrep : Luffs.Runtime.TLSF.FirstBitmapRep first second) (start_fl start_sl : Nat)\n    \
(hstart_sl : start_sl < 32) :\n    \
{}_model\n      \
second first start_fl start_sl = {} second start_fl start_sl := by\n  \
exact Luffs.Runtime.TLSF.findNonemptyClassLowered_refines hrep start_fl start_sl hstart_sl\n\n",
            model.name, model.name, model.refines
        ));
    }
    for model in &module.tlsf_take_candidate_class_models {
        out.push_str(&format!(
            "def {}_model (second : List (BitVec 32)) (first : BitVec 64) (heads next previous : List Nat) (start_fl start_sl : Nat) : Option Luffs.Runtime.TLSF.ClassCandidateResult :=\n  \
{} second first heads next previous start_fl start_sl\n\n",
            model.name, model.refines
        ));
        out.push_str(&format!(
            "theorem {}_refines : {}_model = {} := by rfl\n\n",
            model.name, model.name, model.refines
        ));
    }
    for model in &module.tlsf_mark_free_models {
        out.push_str(&format!(
            "def {}_model (offsets sizes : List Nat) (is_free prev_free : List (Fin 256)) (block returned_offset returned_bytes : Nat) : Option (List (Fin 256) × List (Fin 256)) :=\n  \
{} offsets sizes is_free prev_free block returned_offset returned_bytes\n\n",
            model.name, model.refines
        ));
        out.push_str(&format!(
            "theorem {}_refines : {}_model = {} := by rfl\n\n",
            model.name, model.name, model.refines
        ));
    }
    for model in &module.tlsf_classify_size_models {
        out.push_str(&format!(
            "def {}_model (size : Nat) : Option Nat :=\n  {} size\n\n",
            model.name, model.refines
        ));
        out.push_str(&format!(
            "theorem {}_refines : {}_model = {} := by rfl\n\n",
            model.name, model.name, model.refines
        ));
    }
    for model in &module.tlsf_insert_class_models {
        out.push_str(&format!(
            "def {}_model (second : List (BitVec 32)) (first : BitVec 64) (heads next previous : List Nat) (bin block : Nat) : Option Luffs.Runtime.TLSF.InsertClassResult :=\n  {} second first heads next previous bin block\n\n",
            model.name, model.refines
        ));
        out.push_str(&format!(
            "theorem {}_refines : {}_model = {} := by rfl\n\n",
            model.name, model.name, model.refines
        ));
    }
    for model in &module.tlsf_remove_class_models {
        out.push_str(&format!(
            "def {}_model (second : List (BitVec 32)) (first : BitVec 64) (heads next previous : List Nat) (bin block : Nat) : Option Luffs.Runtime.TLSF.RemoveClassResult :=\n  {} second first heads next previous bin block\n\n",
            model.name, model.refines
        ));
        out.push_str(&format!(
            "theorem {}_refines : {}_model = {} := by rfl\n\n",
            model.name, model.name, model.refines
        ));
    }
    for model in &module.tlsf_deallocate_uncoalesced_models {
        out.push_str(&format!(
            "def {}_model (offsets sizes : List Nat) (is_free prev_free : List (Fin 256)) (second : List (BitVec 32)) (first : BitVec 64) (heads next previous : List Nat) (count block returned_offset returned_bytes : Nat) : Option Luffs.Runtime.TLSF.DeallocateUncoalescedResult :=\n  {} offsets sizes is_free prev_free second first heads next previous count block returned_offset returned_bytes\n\n",
            model.name, model.refines
        ));
        out.push_str(&format!(
            "theorem {}_refines : {}_model = {} := by rfl\n\n",
            model.name, model.name, model.refines
        ));
    }
    for model in &module.tlsf_coalesce_physical_models {
        out.push_str(&format!(
            "def {}_model (offsets sizes : List Nat) (is_free prev_free : List (Fin 256)) (count left : Nat) : Option Luffs.Runtime.TLSF.CoalescePhysicalResult :=\n  {} offsets sizes is_free prev_free count left\n\n",
            model.name, model.refines
        ));
        out.push_str(&format!(
            "theorem {}_refines : {}_model = {} := by rfl\n\n",
            model.name, model.name, model.refines
        ));
    }
    for model in &module.tlsf_coalesce_class_models {
        out.push_str(&format!(
            "def {}_model (offsets sizes : List Nat) (is_free prev_free : List (Fin 256)) (second : List (BitVec 32)) (first : BitVec 64) (heads next previous : List Nat) (count left : Nat) : Option Luffs.Runtime.TLSF.CoalesceClassResult :=\n  {} offsets sizes is_free prev_free second first heads next previous count left\n\n",
            model.name, model.refines
        ));
        out.push_str(&format!(
            "theorem {}_refines : {}_model = {} := by rfl\n\n",
            model.name, model.name, model.refines
        ));
    }
    for model in &module.tlsf_coalesce_if_possible_models {
        out.push_str(&format!(
            "def {}_model (offsets sizes : List Nat) (is_free prev_free : List (Fin 256)) (second : List (BitVec 32)) (first : BitVec 64) (heads next previous : List Nat) (count left : Nat) : Option Luffs.Runtime.TLSF.CoalesceClassResult :=\n  {} offsets sizes is_free prev_free second first heads next previous count left\n\n",
            model.name, model.refines
        ));
        out.push_str(&format!(
            "theorem {}_refines : {}_model = {} := by rfl\n\n",
            model.name, model.name, model.refines
        ));
    }
    for model in &module.tlsf_deallocate_models {
        out.push_str(&format!(
            "def {}_model (offsets sizes : List Nat) (is_free prev_free : List (Fin 256)) (second : List (BitVec 32)) (first : BitVec 64) (heads next previous : List Nat) (count block returned_offset returned_bytes : Nat) : Option Luffs.Runtime.TLSF.CoalesceClassResult :=\n  {} offsets sizes is_free prev_free second first heads next previous count block returned_offset returned_bytes\n\n",
            model.name, model.refines
        ));
        out.push_str(&format!(
            "theorem {}_refines : {}_model = {} := by rfl\n\n",
            model.name, model.name, model.refines
        ));
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
    fn mutable_access_is_parenthesized_for_assignment() {
        let m = parse(
            "fn f(a: &mut [u8], i: usize) -> Option<()> {\nif i >= a.len() { return None; }\na[i] = 1;\nSome(())\n}",
        )
        .unwrap();
        validate(&m).unwrap();
        assert!(m.rust.contains("(*unsafe { a.get_unchecked_mut(i) }) = 1;"));
    }

    #[test]
    fn mutable_access_is_parenthesized_as_method_receiver() {
        let m = parse(
            "fn f(a: &mut [usize], i: usize) -> Option<usize> {\nif i >= a.len() { return None; }\nlet x: usize = a[i].checked_add(1)?;\nSome(x)\n}",
        )
        .unwrap();
        validate(&m).unwrap();
        assert!(
            m.rust
                .contains("(*unsafe { a.get_unchecked_mut(i) }).checked_add(1)?")
        );
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
        assert!(m.proofs[0].facts.iter().any(|fact| fact == "i < input_len"));
    }

    #[test]
    fn if_condition_is_a_fact_inside_the_body() {
        let m = parse(
            "fn f(input: &[u8], i: usize) -> Option<u8> {\nif i < input.len() {\nreturn Some(input[i]);\n}\nNone\n}",
        )
        .unwrap();
        assert!(m.proofs[0].facts.iter().any(|fact| fact == "i < input_len"));
    }

    #[test]
    fn usize_addition_creates_an_overflow_obligation() {
        let m = parse(
            "fn f(a: usize, b: usize) -> Option<usize> {\nif b > usize::MAX - a { return None; }\nlet c: usize = a + b;\nSome(c)\n}",
        )
        .unwrap();
        assert_eq!(m.proofs[0].conclusion, "(a + b) ≤ usize_max");
        assert!(
            m.proofs[0]
                .facts
                .iter()
                .any(|fact| fact == "¬ (b > usize_max - a)")
        );
    }

    #[test]
    fn multiline_explicit_proof_is_collected() {
        let m = parse(
            "fn f(input: &[u8]) -> Option<u8> {\nif input.len() == 0 { return None; }\nproof p: 0 < input.len() by {\nomega\n}\nSome(input[0] by p)\n}",
        )
        .unwrap();
        assert_eq!(m.proofs[0].name, "p");
        assert_eq!(m.proofs[0].body, "omega");
    }

    #[test]
    fn tlsf_runtime_source_has_only_proved_accesses() {
        let m = parse(include_str!("../stdlib/tlsf.luffs")).unwrap();
        validate(&m).unwrap();
        assert!(m.accesses.len() >= 16);
        assert_eq!(
            m.accesses.len(),
            m.proofs
                .iter()
                .filter(|p| p.name.starts_with("__auto_"))
                .count()
        );
        assert!(m.rust.contains("get_unchecked_mut"));
        assert!(m.rust.contains("checked_mul"));
        assert!(m.rust.contains("fn tlsf_find_nonempty_class"));
        assert!(m.rust.contains("fn tlsf_take_candidate_class"));
        assert!(m.rust.contains("[usize; 2048]"));
        assert_eq!(m.tlsf_insert_models.len(), 1);
        assert_eq!(m.tlsf_remove_models.len(), 1);
        assert_eq!(m.tlsf_find_fit_models.len(), 1);
        assert_eq!(m.tlsf_find_nonempty_bin_models.len(), 1);
        assert_eq!(m.tlsf_take_candidate_models.len(), 1);
        assert_eq!(m.tlsf_find_nonempty_class_models.len(), 1);
        assert_eq!(m.tlsf_take_candidate_class_models.len(), 1);
        assert_eq!(m.tlsf_mark_free_models.len(), 1);
        assert_eq!(m.tlsf_classify_size_models.len(), 1);
        assert_eq!(m.tlsf_insert_class_models.len(), 1);
        assert_eq!(m.tlsf_remove_class_models.len(), 1);
        assert_eq!(m.tlsf_deallocate_uncoalesced_models.len(), 1);
        assert_eq!(m.tlsf_coalesce_physical_models.len(), 1);
        assert_eq!(m.tlsf_coalesce_class_models.len(), 1);
        assert_eq!(m.tlsf_coalesce_if_possible_models.len(), 1);
        assert_eq!(m.tlsf_deallocate_models.len(), 1);
        let generated = lean(&m);
        assert!(generated.contains(
            "theorem tlsf_insert_refines : tlsf_insert_model = Luffs.Runtime.TLSF.insertArrays"
        ));
        assert!(generated.contains(
            "theorem tlsf_remove_refines : tlsf_remove_model = Luffs.Runtime.TLSF.removeArrays"
        ));
        assert!(generated.contains(
            "theorem tlsf_find_fit_refines : tlsf_find_fit_model = Luffs.Runtime.TLSF.findFit"
        ));
        assert!(generated.contains(
            "theorem tlsf_find_nonempty_bin_refines : tlsf_find_nonempty_bin_model = Luffs.Runtime.TLSF.findNonemptyBin"
        ));
        assert!(generated.contains(
            "theorem tlsf_take_candidate_refines : tlsf_take_candidate_model = Luffs.Runtime.TLSF.takeCandidateArrays"
        ));
        assert!(generated.contains("theorem tlsf_find_nonempty_class_refines"));
        assert!(generated.contains(
            "theorem tlsf_take_candidate_class_refines : tlsf_take_candidate_class_model = Luffs.Runtime.TLSF.takeCandidateClassArrays"
        ));
        assert!(generated.contains(
            "theorem tlsf_mark_free_refines : tlsf_mark_free_model = Luffs.Runtime.TLSF.markFreeArrays"
        ));
        assert!(generated.contains(
            "theorem tlsf_classify_size_refines : tlsf_classify_size_model = Luffs.Runtime.TLSF.classifySizeBin"
        ));
        assert!(generated.contains(
            "theorem tlsf_insert_class_refines : tlsf_insert_class_model = Luffs.Runtime.TLSF.insertClassArrays"
        ));
        assert!(generated.contains(
            "theorem tlsf_remove_class_refines : tlsf_remove_class_model = Luffs.Runtime.TLSF.removeClassArrays"
        ));
        assert!(generated.contains(
            "theorem tlsf_deallocate_uncoalesced_refines : tlsf_deallocate_uncoalesced_model = Luffs.Runtime.TLSF.deallocateUncoalescedArrays"
        ));
        assert!(generated.contains(
            "theorem tlsf_coalesce_physical_refines : tlsf_coalesce_physical_model = Luffs.Runtime.TLSF.coalescePhysicalArrays"
        ));
        assert!(generated.contains(
            "theorem tlsf_coalesce_class_refines : tlsf_coalesce_class_model = Luffs.Runtime.TLSF.coalesceClassArrays"
        ));
        assert!(generated.contains(
            "theorem tlsf_coalesce_if_possible_refines : tlsf_coalesce_if_possible_model = Luffs.Runtime.TLSF.coalesceIfPossibleArrays"
        ));
        assert!(generated.contains(
            "theorem tlsf_deallocate_refines : tlsf_deallocate_model = Luffs.Runtime.TLSF.deallocateArrays"
        ));
    }

    #[test]
    fn tlsf_public_deallocate_refinement_rejects_missing_left_stage() {
        let source = include_str!("../stdlib/tlsf.luffs")
            .replace("let left: usize = block - 1;", "let left: usize = block;");
        let m = parse(&source).unwrap();
        assert!(m.tlsf_deallocate_models.is_empty());
    }

    #[test]
    fn tlsf_bitmap_refinement_rejects_a_changed_mask() {
        let source =
            include_str!("../stdlib/tlsf.luffs").replace("u64::MAX << bit", "u64::MAX >> bit");
        let m = parse(&source).unwrap();
        assert!(m.tlsf_find_nonempty_bin_models.is_empty());
    }

    #[test]
    fn tlsf_arbitrary_remove_rejects_tail_only_bitmap_clear() {
        let source = include_str!("../stdlib/tlsf.luffs").replace(
            "if predecessor >= next.len() && successor >= next.len() {",
            "if successor >= next.len() {",
        );
        let m = parse(&source).unwrap();
        assert!(m.tlsf_remove_class_models.is_empty());
    }

    #[test]
    fn container_runtime_source_has_only_proved_accesses() {
        let m = parse(include_str!("../stdlib/containers.luffs")).unwrap();
        validate(&m).unwrap();
        assert!(m.accesses.len() >= 10);
        assert_eq!(
            m.accesses.len(),
            m.proofs
                .iter()
                .filter(|p| p.name.starts_with("__auto_"))
                .count()
        );
        assert!(m.rust.contains("get_unchecked_mut"));
        assert!(m.rust.contains("copy_from_slice"));
    }

    #[test]
    fn emits_scalar_function_semantics_from_the_same_source() {
        let m = parse(
            "fn pop_len(len: usize) -> Option<usize> {\nif len == 0 { return None; }\nlet next: usize = len - 1;\nSome(next)\n}",
        )
        .unwrap();
        assert_eq!(m.scalar_models.len(), 1);
        let generated = lean(&m);
        assert!(generated.contains("def pop_len_model (len : Nat) : Option Nat :="));
        assert!(generated.contains("if len = 0 then none else"));
        assert!(generated.contains("let next := len - 1"));
        assert!(generated.contains("some (next)"));
    }

    #[test]
    fn checked_refinement_targets_generated_semantics() {
        let m = parse(
            "// refines Luffs.Runtime.Containers.vecLenAfterPop\nfn vec_len_after_pop(len: usize) -> Option<usize> {\nif len == 0 { return None; }\nlet next_len: usize = len - 1;\nSome(next_len)\n}",
        )
        .unwrap();
        let generated = lean(&m);
        assert!(generated.contains("import Luffs.Runtime.Containers"));
        assert!(generated.contains(
            "theorem vec_len_after_pop_refines : vec_len_after_pop_model = Luffs.Runtime.Containers.vecLenAfterPop"
        ));
    }

    #[test]
    fn emits_mutable_byte_array_semantics_and_refinement() {
        let m = parse(
            "// refines Luffs.Runtime.Containers.vecPushU8\nfn vec_push_u8(storage: &mut [u8], len: usize, capacity: usize, value: u8) -> Option<usize> {\nif len >= capacity { return None; }\nif capacity > storage.len() { return None; }\nstorage[len] = value;\nlet next_len: usize = len + 1;\nSome(next_len)\n}",
        )
        .unwrap();
        assert_eq!(m.array_models.len(), 1);
        let generated = lean(&m);
        assert!(generated.contains(
            "def vec_push_u8_model (storage : List (Fin 256)) (len : Nat) (capacity : Nat) (value : Fin 256)"
        ));
        assert!(generated.contains("let storage := storage.set len value"));
        assert!(generated.contains(
            "theorem vec_push_u8_refines : vec_push_u8_model = Luffs.Runtime.Containers.vecPushU8"
        ));
    }

    #[test]
    fn emits_unit_returning_array_state_semantics() {
        let m = parse(
            "// refines Luffs.Runtime.Containers.boxStoreU8\nfn store(storage: &mut [u8], begin: usize, value: u8) -> Option<()> {\nif begin >= storage.len() { return None; }\nstorage[begin] = value;\nSome(())\n}",
        )
        .unwrap();
        assert_eq!(m.array_models.len(), 1);
        let generated = lean(&m);
        assert!(generated.contains(
            "def store_model (storage : List (Fin 256)) (begin : Nat) (value : Fin 256) : Option (List (Fin 256))"
        ));
        assert!(generated.contains("some (storage)"));
    }

    #[test]
    fn emits_immutable_byte_array_read_semantics() {
        let m = parse(
            "// refines Luffs.Runtime.Containers.boxLoadU8\nfn load(storage: &[u8], begin: usize) -> Option<u8> {\nif begin >= storage.len() { return None; }\nSome(storage[begin])\n}",
        )
        .unwrap();
        assert_eq!(m.read_models.len(), 1);
        let generated = lean(&m);
        assert!(generated.contains(
            "def load_model (storage : List (Fin 256)) (begin : Nat) : Option (Fin 256)"
        ));
        assert!(generated.contains("storage[begin]?"));
        assert!(
            generated
                .contains("theorem load_refines : load_model = Luffs.Runtime.Containers.boxLoadU8")
        );
    }

    #[test]
    fn emits_begin_end_slice_semantics() {
        let m = parse(
            "// refines Luffs.Runtime.Containers.vecSliceU8\nfn slice(storage: &[u8], len: usize, begin: usize, end: usize) -> Option<&[u8]> {\nif begin > end { return None; }\nif end > len { return None; }\nif len > storage.len() { return None; }\nSome(storage[begin..<end])\n}",
        )
        .unwrap();
        assert_eq!(m.read_models.len(), 1);
        let generated = lean(&m);
        assert!(generated.contains("(end_ : Nat) : Option (List (Fin 256))"));
        assert!(generated.contains("some ((storage.drop begin).take (end_ - begin))"));
    }

    #[test]
    fn emits_copy_from_slice_state_semantics() {
        let m = parse(
            "// refines Luffs.Runtime.Containers.vecCopyGrowU8\nfn copy(source: &[u8], destination: &mut [u8], len: usize) -> Option<()> {\nif len > source.len() { return None; }\nif len > destination.len() { return None; }\nlet from: &[u8] = source[0..<len];\nlet to: &mut [u8] = destination[0..<len];\nto.copy_from_slice(from);\nSome(())\n}",
        )
        .unwrap();
        assert_eq!(m.copy_models.len(), 1);
        let generated = lean(&m);
        assert!(generated.contains("some (source.take len ++ destination.drop len)"));
        assert!(generated.contains(
            "theorem copy_refines : copy_model = Luffs.Runtime.Containers.vecCopyGrowU8"
        ));
    }
}
