use std::{collections::HashSet, ops::Range};

use crate::{
    lexer::LexerError,
    semantics::EvalError,
    type_checker::TypeError,
    usage_map::UsageMap,
    util::{pretty::pretty_def, span::Span},
};
use ariadne::{ColorGenerator, IndexType, Label, Report, ReportKind, Source};
use peg::error::ParseError;

#[derive(Debug, Clone)]
pub enum IErr {
    Lexer(LexerError),
    Parser(ParseError<usize>),
    Typing(TypeError),
    Eval(EvalError),
}

pub struct CSource {
    pub path: String,
    pub data: String,
}

pub struct CLabel {
    pub span: Range<usize>,
    pub msg: String,
}

pub fn label(span: Range<usize>, msg: impl AsRef<str>) -> CLabel {
    CLabel {
        span,
        msg: msg.as_ref().to_string(),
    }
}

pub fn trim_span(src: &str, span: Range<usize>) -> Range<usize> {
    if span.start < src.len() && span.end <= src.len() {
        let bytes: Vec<u8> = src.bytes().collect();
        let mut s = span.start;
        loop {
            if bytes[s].is_ascii_whitespace() && s < span.end {
                s += 1;
            } else if bytes[s] == b'#' {
                while s < span.end && bytes[s] != b'\n' {
                    s += 1
                }
            } else {
                break;
            }
        }
        let mut e = span.end;
        loop {
            if e > s && bytes[e - 1].is_ascii_whitespace() {
                e -= 1;
            } else {
                let mut i = e;
                let mut found_comment = false;
                loop {
                    if i <= s || bytes[i - 1] == b'\n' {
                        break;
                    } else if bytes[i - 1] == b'#' {
                        i -= 1;
                        e = i;
                        found_comment = true;
                        break;
                    } else {
                        i -= 1
                    }
                }
                if !found_comment {
                    break;
                }
            }
        }
        Span { start: s, end: e }
    } else {
        span
    }
}

fn report(
    src: &CSource,
    loc: Range<usize>,
    msg: impl AsRef<str>,
    labels: impl IntoIterator<Item = CLabel>,
) {
    let src_content = std::fs::read_to_string(&src.path).unwrap();
    let loc = trim_span(&src_content, loc);
    let mut colors = ColorGenerator::new();
    let a = colors.next();
    Report::build(ReportKind::Error, (&src.path, loc))
        .with_config(ariadne::Config::default().with_index_type(IndexType::Byte))
        .with_message(msg.as_ref())
        .with_labels(labels.into_iter().map(|l| {
            let sp = trim_span(&src_content, l.span);
            Label::new((&src.path, sp))
                .with_message(l.msg)
                .with_color(a)
        }))
        .finish()
        .print((&src.path, Source::from(&src.data)))
        .unwrap();
}

pub fn report_error(src_path: &str, src: &str, e: IErr) {
    let src = CSource {
        path: src_path.to_string(),
        data: src.to_string(),
    };

    match e {
        IErr::Lexer(e) => {
            report(
                &src,
                e.span.clone(),
                "Lexing failed",
                [label(e.span, "Lexer got stuck here")],
            );
        }
        IErr::Parser(e) => {
            report(
                &src,
                e.location..e.location,
                "Parsing failed",
                [label(
                    e.location..e.location,
                    format!("Expected {}", e.expected),
                )],
            );
        }
        IErr::Typing(e) => match e {
            TypeError::UndefinedVariable(x) => {
                report(
                    &src,
                    x.span.clone(),
                    "Type Error",
                    [label(x.span, "Undefined Variable")],
                );
            }
            TypeError::Mismatch(e, t_expected, t_actual) => {
                let expected = match t_expected {
                    Ok(t) => pretty_def(&t.val),
                    Err(t) => t,
                };
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!(
                            "This expression has type {} but should have {}",
                            pretty_def(&t_actual.val),
                            expected,
                        ),
                    )],
                );
            }
            TypeError::Op2Mismatch(e, t_expected, t_actual1, t_actual2) => {
                let expected = match t_expected {
                    Ok(t) => pretty_def(&t.val),
                    Err(t) => t,
                };
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!(
                            "The operands have types '{}' and '{}' but both should have type '{}'",
                            pretty_def(&t_actual1.val),
                            pretty_def(&t_actual2.val),
                            expected,
                        ),
                    )],
                );
            }
            TypeError::MismatchMult(e, t, m_expected, m_actual) => {
                let expected = match m_expected {
                    Ok(m) => pretty_def(&m.val),
                    Err(s) => s,
                };
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!(
                            "This expression has type {} with multiplicity {}, but should have multiplicity {}.",
                                pretty_def(&t.val),
                                pretty_def(&m_actual.val),
                                expected,
                        ),
                    )],
                );
            }
            TypeError::MismatchEffSub(e, p_expected, p_actual) => {
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!(
                            "This expression has effect {}, which is not a subeffect of {}",
                            pretty_def(&p_actual.val),
                            pretty_def(&p_expected.val),
                        ),
                    )],
                );
            }
            TypeError::MismatchEff(e, p_expected, p_actual) => {
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!(
                            "This expression has effect {}, but should have effect {}",
                            pretty_def(&p_actual.val),
                            pretty_def(&p_expected.val),
                        ),
                    )],
                );
            }
            TypeError::MismatchLabel(e, l, t) => {
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!(
                            "The label '{}' is not part of the expected variant type '{}'.",
                            l,
                            pretty_def(&t),
                        ),
                    )],
                );
            }
            TypeError::TypeAnnotationMissing(e) => {
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(e.span, "This expression requires a type annotation")],
                );
            }
            TypeError::CtxSplitFailed(e, ctx, ctx2) => {
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [
                        label(
                            e.span,
                            format!(
                                "In this expression, splitting the context \n    {}\n and rejoining it resulted in a non-subtype context \n    {}",
                                pretty_def(&ctx.simplify()),
                                pretty_def(&ctx2.simplify())
                            )
                        ),
                    ],
                );
            }
            TypeError::CtxCtxSplitFailed(e, ctx, xs) => {
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!(
                            "In this expression, failed to split context {} by free variables {}",
                            pretty_def(&ctx.simplify()),
                            pretty_def(&xs)
                        ),
                    )],
                );
            }
            TypeError::Shadowing(e, x) => {
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!(
                            "In this expression, the variable {} is introduced, which shadows another variable.",
                            pretty_def(&x)
                        ),
                    )],
                );
            }
            TypeError::CtxNotUnr(e, ctx) => {
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!(
                            "This unrestricted lambda abstraction tries to capture a non-unrestricted context {}",
                            pretty_def(&ctx.simplify())
                        ),
                    )],
                );
            }
            TypeError::SeqDropsOrd(e, t) => {
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!(
                            "First sub-expression in sequence needs to have an unrestricted type instead of {}.",
                            pretty_def(&t)
                        ),
                    )],
                );
            }
            TypeError::LeftOverVar(e, x, s, s_used) => {
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!(
                            "This expression binds variable '{}' to session type '{}', but {}",
                            pretty_def(&x),
                            pretty_def(&s),
                            if let Some(s_used) = s_used {
                                format!(
                                    "only the following prefix was used in the body: {}",
                                    pretty_def(&s_used)
                                )
                            } else {
                                format!("the variable was not used in the body.")
                            }
                        ),
                    )],
                );
            }
            TypeError::LeftOverCtx(e, ctx) => {
                let mut xs = HashSet::new();
                ctx.map_binds(&mut |x, t| {
                    if !t.is_unr() {
                        xs.insert(x.clone());
                    }
                });
                let ctx = ctx.restrict(&xs).simplify();
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!(
                            "This expression has unused variables that must be used:  {}",
                            pretty_def(&ctx)
                        ),
                    )],
                );
            }
            TypeError::MultipleClauses(e) => {
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!("Function declarations need exactly one pattern match clause.",),
                    )],
                );
            }
            TypeError::NotEnoughPatterns(e) => {
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!("Wrong amount of patterns for type annotation.",),
                    )],
                );
            }
            TypeError::PatternMismatch(p, t) => {
                report(
                    &src,
                    p.span.clone(),
                    "Type Error",
                    [label(
                        p.span,
                        format!("Pattern does not describe type {}.", pretty_def(&t)),
                    )],
                );
            }
            TypeError::ClauseWithWrongId(e, x, y) => {
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!(
                            "Function clause has name '{}' instead of '{}'.",
                            pretty_def(&x),
                            pretty_def(&y)
                        ),
                    )],
                );
            }
            TypeError::ClauseWithZeroPatterns(e) => {
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!("Function clause needs to have at least one pattern.",),
                    )],
                );
            }
            TypeError::InvalidSplit(e, s, s1) => {
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!(
                            "The expected type {} is not a prefix of the variables type {}.",
                            pretty_def(s1),
                            pretty_def(s)
                        ),
                    )],
                );
            }
            TypeError::CaseDifferentBranchUsageMaps(e, l1, r1, l2, r2) => {
                let pretty_rep = |r: &UsageMap| {
                    let mut s = String::new();
                    for (x, t) in &r.map {
                        s += &format!("  {} : {}\n", x, pretty_def(t));
                    }
                    s
                };
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!(
                            "This case expression uses channels inconsistently in the branches for '{}' and '{}'.\nThe usage map for the branch for '{}' is:\n{}\nThe usage map for the branch for '{}' is:\n{}",
                            l1,
                            l2,
                            l1,
                            pretty_rep(&r1),
                            l2,
                            pretty_rep(&r2),
                        ),
                    )],
                );
            }
            TypeError::IfDifferentBranchUsageMaps(e, r1, r2) => {
                let pretty_rep = |r: &UsageMap| {
                    let mut s = String::new();
                    for (x, t) in &r.map {
                        s += &format!("  {} : {}\n", x, pretty_def(t));
                    }
                    s
                };
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!(
                            "This if-expression uses channels inconsistently across its branches.\nThe usage map for the true-branch is:\n{}\nThe usage map for the false-branch is:\n{}",
                            pretty_rep(&r1),
                            pretty_rep(&r2),
                        ),
                    )],
                );
            }
            TypeError::CaseMissingLabel(e, t, l) => {
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!(
                            "No clause covers label '{}' of type '{}'.",
                            l,
                            pretty_def(t)
                        ),
                    )],
                );
            }
            TypeError::CaseExtraLabel(e, t, l) => {
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!("The label '{}' does not occur in type '{}'. You may want to delete the corresponding clause.", l,  pretty_def(t)),
                    )],
                );
            }
            TypeError::CaseDuplicateLabel(e, _t, l) => {
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!("Multiple cases for the same label '{}'.", l),
                    )],
                );
            }
            TypeError::CaseClauseTypeMismatch(e, t1, t2) => {
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!(
                            "The branches have different types: '{}' is not equal to '{}'.",
                            pretty_def(&t1),
                            pretty_def(&t2)
                        ),
                    )],
                );
            }
            TypeError::CaseLeftOverMismatch(e, x, s1, s2) => {
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!(
                            "The branches use variable '{}' of session type in different ways: '{}' is not the same as {}.",
                            x,
                            pretty_def(&s1),
                            if let Some(s2) = s2 {
                                format!("'{}'", pretty_def(&s2))
                            } else {
                                format!("not using 'x' at all.")
                            }
                        ),
                    )],
                );
            }
            TypeError::VariantEmpty(e) => {
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!("Empty variant types are not allowed."),
                    )],
                );
            }
            TypeError::VariantDuplicateLabel(e, t, l) => {
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!(
                            "Variant type {} contains the label '{}' more than once.",
                            pretty_def(t),
                            l
                        ),
                    )],
                );
            }
            TypeError::RecursiveNonFunctionBinding(e, x) => {
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!(
                            "This expression uses variable '{}' recursively, but '{}' does not have an unrestricted function type.",
                            x.val,
                            x.val,
                        ),
                    )],
                );
            }
            TypeError::WfNonContractive(s, x) => {
                report(
                    &src,
                    s.span.clone(),
                    "Type Error",
                    [label(
                        s.span,
                        format!(
                            "This session type is non-contractive in variable '{}'.",
                            x.val,
                        ),
                    )],
                );
            }
            TypeError::WfEmptyChoice(s) => {
                report(
                    &src,
                    s.span.clone(),
                    "Type Error",
                    [label(
                        s.span,
                        format!("This session type has an empty choice, which is not allowed.",),
                    )],
                );
            }
            TypeError::WfEmptyVariant(t) => {
                report(
                    &src,
                    t.span.clone(),
                    "Type Error",
                    [label(
                        t.span,
                        format!("This variant type is empty, which is not allowed.",),
                    )],
                );
            }
            TypeError::MainReturnsOrd(e, t) => {
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!("Main expression needs to have an unrestricted type, but instead has type '{}'.", pretty_def(t)),
                    )],
                );
            }
            TypeError::WfSessionNotClosed(s, x) => {
                report(
                    &src,
                    s.span.clone(),
                    "Type Error",
                    [label(
                        s.span,
                        format!("Variable '{}' is not bound by a µ-binder. Session types need to be closed.",
                            pretty_def(x)),
                    )],
                );
            }
            TypeError::WfSessionShadowing(s, x) => {
                report(
                    &src,
                    s.span.clone(),
                    "Type Error",
                    [label(
                        s.span,
                        format!("Variable '{}' was already bound further outside. Shadowing is not allowed in session types.",
                            pretty_def(x)),
                    )],
                );
            }
            TypeError::NewWithBorrowedType(e, _s) => {
                report(
                    &src,
                    e.span.clone(),
                    "Type Error",
                    [label(
                        e.span,
                        format!("This expression creates a new channel with a borrowed session type. This is not allowed.",)
                    )],
                );
            }
        },
        IErr::Eval(e) => match e {
            EvalError::ValMismatch(e, v_expected, v_actual) => {
                report(
                    &src,
                    e.span.clone(),
                    "Evaluation Error",
                    [label(
                        e.span,
                        format!(
                            "This expression evaluates to {} but should be {}.",
                            pretty_def(&v_actual),
                            v_expected,
                        ),
                    )],
                );
            }
            EvalError::UndefinedVar(x) => {
                report(
                    &src,
                    x.span.clone(),
                    "Evaluation Error",
                    [label(x.span, format!("This variable is undefined",))],
                );
            }
        },
    }
}
