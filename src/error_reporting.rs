use std::{collections::HashSet, ops::Range};

use crate::{
    lexer::LexerError, semantics::EvalError, type_checker::TypeError, util::pretty::pretty_def,
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

fn report(
    src: &CSource,
    loc: usize,
    msg: impl AsRef<str>,
    labels: impl IntoIterator<Item = CLabel>,
) {
    let mut colors = ColorGenerator::new();
    let a = colors.next();
    Report::build(ReportKind::Error, &src.path, loc)
        .with_config(ariadne::Config::default().with_index_type(IndexType::Byte))
        .with_message(msg.as_ref())
        .with_labels(labels.into_iter().map(|l| {
            Label::new((&src.path, l.span))
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
                e.span.start,
                "Lexing failed",
                [label(e.span, "Lexer got stuck here")],
            );
        }
        IErr::Parser(e) => {
            report(
                &src,
                e.location,
                "Parsing failed",
                [label(
                    e.location..e.location,
                    format!("Expected {}", e.expected),
                )],
            );
        }
        IErr::Typing(e) => match e {
            TypeError::LocationExpr(l) => {
                report(
                    &src,
                    l.span.start,
                    "Type Error",
                    [label(
                        l.span,
                        "Location expressions are not allowed in surface syntax",
                    )],
                );
            }
            TypeError::UndefinedVariable(x) => {
                report(
                    &src,
                    x.span.start,
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
                    e.span.start,
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
            TypeError::MismatchMult(e, t, m_expected, m_actual) => {
                report(
                    &src,
                    e.span.start,
                    "Type Error",
                    [label(
                        e.span,
                        format!(
                            "This expression has type {} with multiplicity {}, but should have multiplicity {}.",
                                pretty_def(&t.val),
                                pretty_def(&m_actual.val),
                                pretty_def(&m_expected.val),
                        ),
                    )],
                );
            }
            TypeError::MismatchEffSub(e, p_expected, p_actual) => {
                report(
                    &src,
                    e.span.start,
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
                    e.span.start,
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
            TypeError::TypeAnnotationMissing(e) => {
                report(
                    &src,
                    e.span.start,
                    "Type Error",
                    [label(e.span, "This expression requires a type annotation")],
                );
            }
            TypeError::CtxSplitFailed(e, ctx, ctx2) => {
                report(
                    &src,
                    e.span.start,
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
                    e.span.start,
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
                    e.span.start,
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
                    e.span.start,
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
                    e.span.start,
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
                    e.span.start,
                    "Type Error",
                    [label(
                        e.span,
                        format!(
                            "Leaf expression has unused variables that must be used: {}",
                            pretty_def(&ctx)
                        ),
                    )],
                );
            }
            TypeError::MultipleClauses(e) => {
                report(
                    &src,
                    e.span.start,
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
                    e.span.start,
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
                    p.span.start,
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
                    e.span.start,
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
                    e.span.start,
                    "Type Error",
                    [label(
                        e.span,
                        format!("Function clause needs to have at least one pattern.",),
                    )],
                );
            }
        },
        IErr::Eval(e) => match e {
            //EvalError::ValMismatch(e, v_expected, v_actual) => {
            //    report(
            //        &src,
            //        e.span.start,
            //        "Evaluation Error",
            //        [label(
            //            e.span,
            //            format!(
            //                "This expression evaluates to {} but should be {}.",
            //                pretty_def(&v_actual),
            //                v_expected,
            //            ),
            //        )],
            //    );
            //}
            //EvalError::UndefinedLoc(e, l) => {
            //    report(
            //        &src,
            //        e.span.start,
            //        "Evaluation Error",
            //        [label(
            //            e.span,
            //            format!("This expression evaluated to the undefined location {}.", l,),
            //        )],
            //    );
            //}
            //EvalError::ClosedUnfinished(e, r, w) => {
            //    report(
            //        &src,
            //        e.span.start,
            //        "Evaluation Error",
            //        [label(
            //            e.span,
            //            format!(
            //                "This expression tries to close a resource of type {} with unfinished or invalid output '{}'.",
            //                pretty_def(&r),
            //                pretty_def(&w),
            //            ),
            //        )],
            //    );
            //}
            //EvalError::UndefinedVar(x) => {
            //    report(
            //        &src,
            //        x.span.start,
            //        "Evaluation Error",
            //        [label(x.span, format!("This variable is undefined",))],
            //    );
            //}
            //EvalError::InvalidWrite(e, r, r1) => {
            //    report(
            //        &src,
            //        e.span.start,
            //        "Evaluation Error",
            //        [label(
            //            e.span,
            //            format!(
            //                "This expression perform an operation {} which is invalid on a resource of type {}.",
            //                pretty_def(&r1),
            //                pretty_def(&r),
            //            ),
            //        )],
            //    );
            //}
            //EvalError::NonEmptyHeap(heap) => {
            //    report(
            //        &src,
            //        0,
            //        format!(
            //            "Evaluation Error: Program terminated with non-empty heap:\n{}",
            //            pretty_def(&heap)
            //        ),
            //        [],
            //    );
            //}
            //EvalError::AppWithoutAnn(e) => {
            //    report(
            //        &src,
            //        e.span.start,
            //        "Evaluation Error",
            //        [label(
            //            e.span,
            //            "This application does not have a multiplicity annotation.",
            //        )],
            //    );
            //}
        },
    }
}
