use std::collections::HashSet;

use crate::{
    syntax::{
        Eff, Expr, Id, Mult, Pattern, SEff, SExpr, SId, SLoc, SMult, SPattern, SRegex, SType, Type,
    },
    type_context::{ext, Ctx, CtxS, JoinOrd},
    util::span::fake_span,
};

#[derive(Debug, Clone)]
pub enum TypeError {
    LocationExpr(SLoc),
    UndefinedVariable(SId),
    Mismatch(SExpr, Result<SType, String>, SType),
    MismatchMult(SExpr, SType, SMult, SMult),
    MismatchEff(SExpr, SEff, SEff),
    MismatchEffSub(SExpr, SEff, SEff),
    TypeAnnotationMissing(SExpr),
    ClosedUnfinished(SExpr, SRegex),
    InvalidWrite(SExpr, SRegex, SRegex),
    InvalidSplitArg(SRegex),
    InvalidSplitRes(SExpr, SRegex, SRegex, SRegex),
    CtxSplitFailed(SExpr, Ctx, Ctx),
    CtxCtxSplitFailed(SExpr, Ctx, HashSet<Id>),
    Shadowing(SExpr, SId),
    CtxNotUnr(SExpr, Ctx),
    NewEmpty(SRegex),
    SeqDropsOrd(SExpr, SType),
    LeftOverCtx(SExpr, Ctx),
    MultipleClauses(SExpr),
    NotEnoughPatterns(SExpr),
    PatternMismatch(SPattern, SType),
    ClauseWithWrongId(SExpr, SId, SId),
    ClauseWithZeroPatterns(SExpr),
}

// TODO: Subtyping

pub fn check(ctx: &Ctx, e: &mut SExpr, t: &SType) -> Result<Eff, TypeError> {
    let e_copy = e.clone();
    match &mut e.val {
        Expr::Loc(l) => Err(TypeError::LocationExpr(l.clone())),
        Expr::Abs(om, x, e_body) => match &t.val {
            Type::Arr(m, p, t1, t2) => {
                if let Some(m2) = om {
                    if m.val != m2.val {
                        Err(TypeError::MismatchMult(
                            e_copy.clone(),
                            t.clone(),
                            m.clone(),
                            m2.clone(),
                        ))?
                    }
                }

                if m.val == Mult::Unr && !ctx.is_unr() {
                    Err(TypeError::CtxNotUnr(e_copy.clone(), ctx.clone()))?
                }
                if ctx.vars().contains(&x.val) {
                    Err(TypeError::Shadowing(e_copy.clone(), x.clone()))?
                }
                let ctx2 = ext(
                    m.val,
                    ctx.clone(),
                    Ctx::Bind(x.clone(), t1.as_ref().clone()),
                );
                let po = check(&ctx2, e_body, t2)?;
                if Eff::leq(po, p.val) {
                    Ok(Eff::No)
                } else {
                    Err(TypeError::MismatchEffSub(
                        *e_body.clone(),
                        p.clone(),
                        fake_span(po),
                    ))
                }
            }
            _ => Err(TypeError::Mismatch(
                e.clone(),
                Err(format!("function type")),
                t.clone(),
            )),
        },
        _ => {
            let (t2, p) = infer(ctx, e)?;
            if t.val.is_equal_to(&t2.val) {
                Ok(p)
            } else {
                Err(TypeError::Mismatch(e.clone(), Ok(t.clone()), t2))
            }
        }
    }
}

pub fn infer(ctx: &Ctx, e: &mut SExpr) -> Result<(SType, Eff), TypeError> {
    let e_copy = e.clone();
    match &mut e.val {
        Expr::Unit => {
            assert_unr_ctx(&e_copy, &ctx)?;
            Ok((fake_span(Type::Unit), Eff::No))
        }
        Expr::New(r) if r.is_empty() => Err(TypeError::NewEmpty(r.clone()))?,
        Expr::New(r) => {
            assert_unr_ctx(&e_copy, &ctx)?;
            Ok((fake_span(Type::Regex(r.clone())), Eff::No))
        }
        Expr::Write(w, e2) => {
            let (t, _p) = infer(ctx, e2)?;
            match &t.val {
                Type::Regex(r) => {
                    let r2 = r.deriv_re_norm(&w.val);
                    if r2.is_empty() {
                        Err(TypeError::InvalidWrite(e_copy, r.clone(), w.clone()))
                    } else {
                        Ok((fake_span(Type::Regex(fake_span(r2))), Eff::Yes))
                    }
                }
                _ => Err(TypeError::Mismatch(
                    e.clone(),
                    Err(format!("resource type")),
                    t.clone(),
                )),
            }
        }
        Expr::Split(r1, e2) => {
            let (t, p) = infer(ctx, e2)?;
            match &t.val {
                Type::Regex(r) => {
                    let r2 = r.deriv_re_norm(r1);
                    if r1.is_empty() {
                        Err(TypeError::InvalidSplitArg(r1.clone()))
                    } else if r2.is_empty() {
                        Err(TypeError::InvalidSplitRes(
                            e_copy,
                            r.clone(),
                            r1.clone(),
                            fake_span(r2.clone()),
                        ))
                    } else {
                        Ok((
                            fake_span(Type::Prod(
                                fake_span(Mult::OrdL),
                                Box::new(fake_span(Type::Regex(r1.clone()))),
                                Box::new(fake_span(Type::Regex(fake_span(r2)))),
                            )),
                            p,
                        ))
                    }
                }
                _ => Err(TypeError::Mismatch(
                    e.clone(),
                    Err(format!("resource type")),
                    t.clone(),
                )),
            }
        }
        Expr::Drop(e2) => {
            let (t, p) = infer(ctx, e2)?;
            match &t.val {
                Type::Regex(r) if r.nullable() => Ok((fake_span(Type::Unit), p)),
                Type::Regex(r) => Err(TypeError::ClosedUnfinished(e2.as_ref().clone(), r.clone())),
                _ => Err(TypeError::Mismatch(
                    e.clone(),
                    Err(format!("resource type")),
                    t.clone(),
                )),
            }
        }
        Expr::Loc(l) => Err(TypeError::LocationExpr(l.clone())),
        // TODO: This check is not necessary anymore, because contexts
        // contain exactly the free variables.
        Expr::Var(x) => match ctx.lookup_ord_pure(x) {
            Some((ctx, t)) => {
                assert_unr_ctx(e, &ctx)?;
                Ok((t.clone(), Eff::No))
            }
            None => Err(TypeError::UndefinedVariable(x.clone())),
        },
        Expr::Abs(_m, _x, _e) => Err(TypeError::TypeAnnotationMissing(e.clone())),
        Expr::App(om, e1, e2) => {
            let c1 = ctx.restrict(&e1.free_vars());
            let c2 = ctx.restrict(&e2.free_vars());
            let (t1, p1) = infer(&c1, e1)?;
            let (t2, p2) = infer(&c2, e2)?;
            match t1.val {
                Type::Arr(m, p, t11, t12) if t11.val.is_equal_to(&t2.val) => {
                    match m.val {
                        Mult::OrdL if p2 == Eff::Yes => Err(TypeError::MismatchEff(
                            *e2.clone(),
                            fake_span(Eff::No),
                            fake_span(p2),
                        ))?,
                        Mult::OrdR if p1 == Eff::Yes => Err(TypeError::MismatchEff(
                            *e1.clone(),
                            fake_span(Eff::No),
                            fake_span(p1),
                        ))?,
                        _ => (),
                    }
                    let c12 = match m.val {
                        Mult::Unr => CtxS::Join(c1.clone(), c2.clone(), JoinOrd::Ordered),
                        Mult::Lin => CtxS::Join(c1.clone(), c2.clone(), JoinOrd::Unordered),
                        Mult::OrdL => CtxS::Join(c1.clone(), c2.clone(), JoinOrd::Ordered),
                        Mult::OrdR => CtxS::Join(c2.clone(), c1.clone(), JoinOrd::Ordered),
                    };
                    if !ctx.is_subctx_of(&c12) {
                        Err(TypeError::CtxSplitFailed(e_copy, ctx.clone(), c12.clone()))?
                    }
                    *om = Some(m.val);
                    Ok((*t12, Eff::lub(p.val, Eff::lub(p1, p2))))
                }
                Type::Arr(_m, _p, t11, _t12) => Err(TypeError::Mismatch(
                    *e2.clone(),
                    Ok(*t11.clone()),
                    t2.clone(),
                ))?,
                _ => Err(TypeError::Mismatch(
                    *e1.clone(),
                    Err("Function".into()),
                    t1.clone(),
                )),
            }
        }
        Expr::AppBorrow(_e1, _x) => {
            panic!("Borrows are not supported, yet")
            ////////////////////////////////////////////////////////////////////////////////
            // Translating borrow notation is nonlocal:
            //   The code

            //     let x = new {ab} in (f &x; close (!b) x)

            //   needs to be translated to

            //     let x = new {ab} in let (y , x) = split a x in (f y; close (!b) x)

            //   instead of

            //     let x = new {ab} in (let (y , x) = split a x in f y); close (!b) x

            //   We cannot do it as a preprocessing because, we need type checker information.
            //   We cannot do it directly in the typechecker without changing the shape of the relation.
            ////////////////////////////////////////////////////////////////////////////////

            // let c1 = {
            //     let mut xs = ctx.vars();
            //     xs.remove(&x.val);
            //     ctx.restrict(&xs)
            // };
            // // let c2 = ctx.restrict(&HashSet::from([x.val.clone()]));

            // let (t, _) = infer(&c1, &e1)?;
            // let r = match &t.val {
            //     Type::Arr(_m, _p, t1, _t2) => match &t1.val {
            //         Type::Regex(r) => r.clone(),
            //         t => Err(TypeError::Mismatch(
            //             *e1.clone(),
            //             Err(format!("function type with resource domain")),
            //             fake_span(t.clone()),
            //         ))?,
            //     },
            //     t => Err(TypeError::Mismatch(
            //         *e1.clone(),
            //         Err(format!("function type")),
            //         fake_span(t.clone()),
            //     ))?,
            // };

            // let y = fresh_var();
            // let e_new = fake_span(Expr::LetPair(
            //     y.clone(),
            //     x.clone(),
            //     Box::new(fake_span(Expr::Split(
            //         r,
            //         Box::new(fake_span(Expr::Var(x.clone()))),
            //     ))),
            //     Box::new(fake_span(Expr::App(
            //         e1.clone(),
            //         Box::new(fake_span(Expr::Var(y))),
            //     ))),
            // ));
            // eprintln!("BORROW BORROW BORROW");
            // eprintln!("Expression In: {}", pretty_def(&e));
            // eprintln!("Expression Out: {}", pretty_def(&e_new));
            // eprintln!("Context: {}", pretty_def(&ctx.simplify()));
            // infer(ctx, &e_new)
        }
        Expr::Pair(om, e1, e2) => {
            let c1 = ctx.restrict(&e1.free_vars());
            let c2 = ctx.restrict(&e2.free_vars());
            let (t1, p1) = infer(&c1, e1)?;
            let (t2, p2) = infer(&c2, e2)?;

            let m = {
                let c12_lin = CtxS::Join(c1.clone(), c2.clone(), JoinOrd::Unordered);
                if ctx.is_subctx_of(&c12_lin) {
                    Mult::Lin
                } else {
                    let c12_ordl = CtxS::Join(c1.clone(), c2.clone(), JoinOrd::Ordered);
                    if ctx.is_subctx_of(&c12_ordl) {
                        Mult::OrdL
                    } else {
                        Err(TypeError::CtxSplitFailed(
                            e_copy.clone(),
                            ctx.clone(),
                            c12_ordl.clone(),
                        ))?
                    }
                }
            };

            match m {
                Mult::OrdL if t1.is_ord() && p2 == Eff::Yes => Err(TypeError::MismatchEff(
                    *e2.clone(),
                    fake_span(Eff::No),
                    fake_span(p2),
                ))?,
                Mult::OrdR if t2.is_ord() && p1 == Eff::Yes => Err(TypeError::MismatchEff(
                    *e1.clone(),
                    fake_span(Eff::No),
                    fake_span(p1),
                ))?,
                _ => (),
            }

            let t_pair = fake_span(Type::Prod(fake_span(m), Box::new(t1), Box::new(t2)));

            if let Some(m2) = om {
                if m != m2.val {
                    Err(TypeError::MismatchMult(
                        e_copy,
                        t_pair.clone(),
                        fake_span(m),
                        m2.clone(),
                    ))?
                }
            }

            Ok((t_pair, Eff::lub(p1, p2)))
        }
        Expr::LetPair(x, y, e1, e2) => {
            let (cc, c) = match ctx.split(&e1.free_vars()) {
                Some((cc, c)) => (cc, c),
                None => Err(TypeError::CtxCtxSplitFailed(
                    e_copy.clone(),
                    ctx.clone(),
                    e1.free_vars(),
                ))?,
            };
            let (t1, p1) = infer(&c, e1)?;
            if p1 == Eff::Yes {
                Err(TypeError::MismatchEff(
                    *e1.clone(),
                    fake_span(Eff::No),
                    fake_span(p1),
                ))?
            }
            let (m, t11, t12) = match t1.val {
                Type::Prod(m, t11, t12) => (m, *t11, *t12),
                _ => Err(TypeError::Mismatch(
                    e_copy.clone(),
                    Err(format!("product type")),
                    t1,
                ))?,
            };
            let c_fill = ext(
                m.val,
                CtxS::Bind(x.clone(), t11),
                CtxS::Bind(y.clone(), t12),
            );

            let ctx_vars = cc.fill(Ctx::Empty).vars();
            if ctx_vars.contains(&x.val) {
                Err(TypeError::Shadowing(e_copy.clone(), x.clone()))?
            }
            if ctx_vars.contains(&y.val) || x.val == y.val {
                Err(TypeError::Shadowing(e_copy.clone(), y.clone()))?
            }

            let ctx2 = &cc.fill(c_fill);
            infer(ctx2, e2)
        }
        Expr::Ann(e, t) => {
            let eff = check(ctx, e, t)?;
            Ok((t.clone(), eff))
        }
        Expr::Let(x, e1, e2) => {
            let c1 = ctx.restrict(&e1.free_vars());
            let c2 = ctx.restrict(&e2.free_vars());

            if c2.vars().contains(&x.val) {
                Err(TypeError::Shadowing(e_copy.clone(), x.clone()))?
            }

            let join_ord = {
                let c12 = CtxS::Join(c1.clone(), c2.clone(), JoinOrd::Unordered);
                if ctx.is_subctx_of(&c12) {
                    JoinOrd::Unordered
                } else {
                    let c12 = CtxS::Join(c1.clone(), c2.clone(), JoinOrd::Ordered);
                    if ctx.is_subctx_of(&c12) {
                        JoinOrd::Ordered
                    } else {
                        Err(TypeError::CtxSplitFailed(
                            e_copy.clone(),
                            ctx.clone(),
                            c12.clone(),
                        ))?
                    }
                }
            };

            let (t1, p1) = infer(&c1, e1)?;
            let c2x = CtxS::Join(CtxS::Bind(x.clone(), t1), &c2, join_ord);
            let (t2, p2) = infer(&c2x, e2)?;
            Ok((t2, Eff::lub(p1, p2)))
        }
        Expr::Seq(e1, e2) => {
            let c1 = ctx.restrict(&e1.free_vars());
            let c2 = ctx.restrict(&e2.free_vars());

            let (t1, p1) = infer(&c1, e1)?;
            let (t2, p2) = infer(&c2, e2)?;

            if t1.is_ord() {
                Err(TypeError::SeqDropsOrd(e.clone(), t1.clone()))?
            }

            let c12 = CtxS::Join(c1.clone(), c2.clone(), JoinOrd::Ordered);
            if !ctx.is_subctx_of(&c12) {
                Err(TypeError::CtxSplitFailed(
                    e.clone(),
                    ctx.clone(),
                    c12.clone(),
                ))?
            }
            Ok((t2, Eff::lub(p1, p2)))
        }
        Expr::LetDecl(x, t, cs, e) => {
            let c = if cs.len() == 1 {
                cs.first_mut().unwrap()
            } else {
                Err(TypeError::MultipleClauses(e_copy.clone()))?
            };
            if c.id.val != x.val {
                Err(TypeError::ClauseWithWrongId(
                    e_copy.clone(),
                    c.id.clone(),
                    x.clone(),
                ))?
            }
            let (arg_tys, ret_ty, ret_eff) = split_arrow_type(t);
            let ret_eff = if let Some(ret_eff) = ret_eff {
                ret_eff
            } else {
                Err(TypeError::ClauseWithZeroPatterns(e_copy.clone()))?
            };
            if c.pats.len() != arg_tys.len() {
                Err(TypeError::NotEnoughPatterns(e_copy.clone()))?
            }
            let mut ctx_body = ctx.clone();
            for (pat, (arg_ty, m)) in c.pats.iter().zip(arg_tys) {
                ctx_body = ext(m.val, ctx_body, check_pattern(pat, &arg_ty)?);
            }
            let eff = check(&ctx_body, &mut c.val.body, &ret_ty)?;
            if !Eff::leq(eff, ret_eff.val) {
                Err(TypeError::MismatchEffSub(
                    e_copy.clone(),
                    fake_span(eff),
                    ret_eff,
                ))?
            }
            let ctx = CtxS::Join(CtxS::Bind(x.clone(), t.clone()), ctx, JoinOrd::Ordered);
            infer(&ctx, e)
        }
    }
}

pub fn check_pattern(pat: &SPattern, t: &SType) -> Result<Ctx, TypeError> {
    match (&pat.val, &t.val) {
        (Pattern::Var(x), _) => Ok(Ctx::Bind(x.clone(), t.clone())),
        (Pattern::Pair(pat1, pat2), Type::Prod(m, t1, t2)) => {
            let c1 = check_pattern(pat1, t1)?;
            let c2 = check_pattern(pat2, t2)?;
            Ok(ext(m.val, c1, c2))
        }
        (Pattern::Pair(pat1, pat2), _) => Err(TypeError::PatternMismatch(pat.clone(), t.clone())),
    }
}

pub fn split_arrow_type(mut t: &SType) -> (Vec<(SType, SMult)>, SType, Option<SEff>) {
    let mut args = vec![];
    let mut eff = None;
    loop {
        match &t.val {
            Type::Arr(m, e, t1, t2) => {
                t = t2;
                eff = Some(e.clone());
                args.push((t1.as_ref().clone(), m.clone()));
            }
            _ => return (args, t.clone(), eff),
        }
    }
}

pub fn infer_type(e: &mut SExpr) -> Result<(SType, Eff), TypeError> {
    infer(&Ctx::Empty, e)
}

pub fn assert_unr_ctx(e: &SExpr, ctx: &Ctx) -> Result<(), TypeError> {
    if ctx.is_unr() {
        Ok(())
    } else {
        Err(TypeError::LeftOverCtx(e.clone(), ctx.clone()))
    }
}
