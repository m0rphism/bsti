use std::collections::{HashMap, HashSet};

use crate::{
    ren::Ren,
    rep::Rep,
    syntax::{
        Eff, Expr, Id, Mult, Op1, Op2, Pattern, SClause, SEff, SExpr, SId, SLoc, SMult, SPattern,
        SSession, SSessionB, SType, Session, SessionB, SessionO, SessionOp, SumLabel, Type,
    },
    type_context::{ext, Ctx, CtxCtx, CtxS, JoinOrd},
    util::{pretty::pretty_def, span::fake_span},
};

#[derive(Debug, Clone)]
pub enum TypeError {
    LocationExpr(SLoc),
    UndefinedVariable(SId),
    Mismatch(SExpr, Result<SType, String>, SType),
    MismatchMult(SExpr, SType, Result<SMult, String>, SMult),
    MismatchEff(SExpr, SEff, SEff),
    MismatchEffSub(SExpr, SEff, SEff),
    MismatchLabel(SExpr, SumLabel, SType),
    Op2Mismatch(SExpr, Result<SType, String>, SType, SType),
    TypeAnnotationMissing(SExpr),
    //ClosedUnfinished(SExpr, SRegex),
    //InvalidWrite(SExpr, SRegex, SRegex),
    InvalidSplit(SExpr, SSession, SSessionB),
    //InvalidSplitArg(SRegex),
    //InvalidSplitRes(SExpr, SRegex, SRegex, SRegex),
    CtxSplitFailed(SExpr, Ctx, Ctx),
    CtxCtxSplitFailed(SExpr, Ctx, HashSet<Id>),
    Shadowing(SExpr, SId),
    CtxNotUnr(SExpr, Ctx),
    SeqDropsOrd(SExpr, SType),
    LeftOverVar(SExpr, SId, SSession, Option<Session>),
    LeftOverCtx(SExpr, Ctx),
    MultipleClauses(SExpr),
    NotEnoughPatterns(SExpr),
    PatternMismatch(SPattern, SType),
    ClauseWithWrongId(SExpr, SId, SId),
    ClauseWithZeroPatterns(SExpr),
    CaseMissingLabel(SExpr, SType, SumLabel),
    CaseExtraLabel(SExpr, SType, SumLabel),
    CaseDuplicateLabel(SExpr, SType, SumLabel),
    CaseClauseTypeMismatch(SExpr, SType, SType),
    CaseLeftOverMismatch(SExpr, Id, Session, Option<Session>),
    VariantEmpty(SExpr),
    VariantDuplicateLabel(SExpr, SType, SumLabel),
    RecursiveNonFunctionBinding(SExpr, SId),
}

pub fn if_chan_then_used(e: &SExpr, t: &SType, u: &Rep, x: &SId) -> Result<(), TypeError> {
    match &t.val {
        Type::Chan(s) => {
            if let Some(s2) = u.map.get(&x.val) {
                if **s != *s2 {
                    Err(TypeError::LeftOverVar(
                        e.clone(),
                        x.clone(),
                        s.clone(),
                        Some(s2.clone()),
                    ))
                } else {
                    Ok(())
                }
            } else {
                Err(TypeError::LeftOverVar(
                    e.clone(),
                    x.clone(),
                    s.clone(),
                    None,
                ))
            }
        }
        _ => Ok(()),
    }
}

pub fn split_infos(fvs: &HashSet<Id>, u: &Rep) -> HashMap<Id, SessionB> {
    let mut sis = HashMap::new();
    for x in fvs {
        if let Some(Session::Borrowed(s)) = u.map.get(x) {
            sis.insert(x.clone(), s.val.clone());
        }
    }
    sis
}

pub fn rename_vars(r: &Ren, xs: &HashSet<Id>) -> HashSet<Id> {
    let mut out = HashSet::new();
    for x in xs {
        if let Some(y) = r.map.get(x) {
            out.insert(y.clone());
        }
        out.insert(x.clone());
    }
    out
}

pub fn intersection<T: std::hash::Hash + Eq + Clone>(
    xss: impl IntoIterator<Item = HashSet<T>>,
) -> HashSet<T> {
    let xss: Vec<_> = xss.into_iter().collect();
    if xss.len() == 0 {
        return HashSet::new();
    }
    let mut it = xss.into_iter();
    let mut out = it.next().unwrap().clone();
    for xs in it {
        out = out.intersection(&xs).cloned().collect();
    }
    out
}

pub fn union<T: std::hash::Hash + Eq + Clone>(
    xss: impl IntoIterator<Item = HashSet<T>>,
) -> HashSet<T> {
    let mut out = HashSet::new();
    for xs in xss {
        out = out.union(&xs).cloned().collect();
    }
    out
}

pub fn check_split_alg_gen(
    e: &SExpr,
    u1: &Rep,
    u2: &Rep,
    fvs1: &HashSet<Id>,
    fvs2: &HashSet<Id>,
    ctx: &Ctx,
    ctx1: &Ctx,
    cc2: &CtxCtx,
) -> Result<(), TypeError> {
    let fvs: HashSet<Id> = fvs1.intersection(&fvs2).cloned().collect();
    let sis = split_infos(&fvs, &u1);
    let r1 = Ren::fresh_from(sis.keys(), "1");
    let r2 = Ren::fresh_from(sis.keys(), "2");
    let u = u1.join(u2);
    let ctx_split = ctx.replace(&u).split_ctx(&sis, &r1, &r2);

    let c12 = cc2
        .replace(u2)
        .rename(&r2)
        .fill(ctx1.replace(u1).rename(&r1));
    if !ctx_split.is_subctx_of(&c12) {
        Err(TypeError::CtxSplitFailed(
            e.clone(),
            ctx_split.clone(),
            c12.clone(),
        ))?
    }
    Ok(())
}

pub fn check_split_alg(
    e: &SExpr,
    u1: &Rep,
    u2: &Rep,
    fvs1: &HashSet<Id>,
    fvs2: &HashSet<Id>,
    ctx: &Ctx,
    ctx1: &Ctx,
    ctx2: &Ctx,
    o: JoinOrd,
) -> Result<(), TypeError> {
    let cc2 = CtxCtx::JoinL(Box::new(CtxCtx::Hole), Box::new(ctx2.clone()), o);
    check_split_alg_gen(e, u1, u2, fvs1, fvs2, ctx, ctx1, &cc2)
}

pub fn compute_ctx_ctx(
    e: &SExpr,
    u1: &Rep,
    fvs1: &HashSet<Id>,
    fvs2: &HashSet<Id>,
    ctx: &Ctx,
) -> Result<CtxCtx, TypeError> {
    let fvs: HashSet<Id> = fvs1.intersection(&fvs2).cloned().collect();
    let sis = split_infos(&fvs, &u1);
    let r1 = Ren::fresh_from(sis.keys(), "1");
    let r2 = Ren::fresh_from(sis.keys(), "2");
    let ctx_split = ctx.split_ctx(&sis, &r1, &r2);
    let fvs1r1 = rename_vars(&r1, &fvs1);
    let (cc, _) = match ctx_split.split(&fvs1r1) {
        Some((cc, c)) => (cc, c),
        None => Err(TypeError::CtxCtxSplitFailed(
            e.clone(),
            ctx_split.clone(),
            fvs1r1,
        ))?,
    };
    let cc = cc.rename(&r2.invert());
    Ok(cc)
}

pub fn check_variant_label_eq(
    e: &SExpr,
    t: &SType,
    actual: &[&SumLabel],
    expected: &[&SumLabel],
) -> Result<(), TypeError> {
    if actual.len() == 0 {
        return Err(TypeError::VariantEmpty(e.clone()));
    }
    for l in actual {
        if !expected.contains(l) {
            return Err(TypeError::CaseExtraLabel(
                e.clone(),
                t.clone(),
                (*l).clone(),
            ));
        }
    }
    for l in expected {
        if !actual.contains(l) {
            return Err(TypeError::CaseMissingLabel(
                e.clone(),
                t.clone(),
                (*l).clone(),
            ));
        }
    }
    for (i, l) in actual.iter().enumerate() {
        if i != actual.len() {
            if (&actual[i + 1..]).contains(l) {
                return Err(TypeError::CaseDuplicateLabel(
                    e.clone(),
                    t.clone(),
                    (*l).clone(),
                ));
            }
        }
    }
    for (i, l) in expected.iter().enumerate() {
        if i != expected.len() {
            if (&expected[i + 1..]).contains(l) {
                return Err(TypeError::VariantDuplicateLabel(
                    e.clone(),
                    t.clone(),
                    (*l).clone(),
                ));
            }
        }
    }
    Ok(())
}

pub fn check_rep_eq(e: &SExpr, u1: &Rep, u2: &Rep) -> Result<(), TypeError> {
    for (x, s1) in &u1.map {
        if let Some(s2) = u2.map.get(x) {
            if !s1.eq(s2) {
                return Err(TypeError::CaseLeftOverMismatch(
                    e.clone(),
                    x.clone(),
                    s1.clone(),
                    Some(s2.clone()),
                ));
            }
        } else {
            return Err(TypeError::CaseLeftOverMismatch(
                e.clone(),
                x.clone(),
                s1.clone(),
                None,
            ));
        }
    }
    for (x, s2) in &u2.map {
        if !u1.map.contains_key(x) {
            return Err(TypeError::CaseLeftOverMismatch(
                e.clone(),
                x.clone(),
                s2.clone(),
                None,
            ));
        }
    }
    Ok(())
}

pub fn check(ctx: &Ctx, e: &SExpr, t: &SType) -> Result<(Rep, Eff), TypeError> {
    match &e.val {
        Expr::Abs(x, e_body) => match &t.val {
            Type::Arr(m, p, t1, t2) => {
                // For unrestricted lambdas: ensure that context is unrestricted.
                if m.val == Mult::Unr && !ctx.is_unr() {
                    Err(TypeError::CtxNotUnr(e.clone(), ctx.clone()))?
                }
                // Assert that `x` is not in the context.
                if ctx.vars().contains(&x.val) {
                    Err(TypeError::Shadowing(e.clone(), x.clone()))?
                }
                // Check the body in the extended context.
                let ctx2 = ext(
                    m.val,
                    ctx.clone(),
                    Ctx::Bind(x.clone(), t1.as_ref().clone()),
                );
                let (u, po) = check(&ctx2, e_body, t2)?;
                // Assert that channel arguments are used up.
                if_chan_then_used(&e, &t1, &u, &x)?;
                // Assert that the effects are correct
                if !Eff::leq(po, p.val) {
                    return Err(TypeError::MismatchEffSub(
                        *e_body.clone(),
                        p.clone(),
                        fake_span(po),
                    ));
                }
                Ok((u.remove(x), Eff::No))
            }
            _ => Err(TypeError::Mismatch(
                e.clone(),
                Err(format!("function type")),
                t.clone(),
            )),
        },
        Expr::Borrow(x) => {
            // Assert that `t` is a borrowed session type
            let s1 = match &t.val {
                Type::Chan(s) => match &s.val {
                    Session::Borrowed(s) => s,
                    _ => {
                        return Err(TypeError::Mismatch(
                            e.clone(),
                            Err("Chan with borrowed session type".to_owned()),
                            t.clone(),
                        ))
                    }
                },
                _ => {
                    return Err(TypeError::Mismatch(
                        e.clone(),
                        Err("Chan".to_owned()),
                        t.clone(),
                    ))
                }
            };
            // Lookup type of `x`
            let tx = match ctx.lookup_ord_pure(x) {
                Some((ctx, t)) => {
                    assert_unr_ctx(e, &ctx)?;
                    t
                }
                None => return Err(TypeError::UndefinedVariable(x.clone())),
            };
            // Assert that type of `x` is a channel
            let s = match &tx.val {
                Type::Chan(s) => s,
                _ => {
                    // TODO
                    return Err(TypeError::Mismatch(
                        e.clone(),
                        Err("Chan".to_owned()),
                        t.clone(),
                    ));
                }
            };
            // Assert that the `s % s1` is defined
            if let Some(_s2) = s.split(s1) {
                let u = Rep::single(x.val.clone(), Session::Borrowed(s1.clone()));
                Ok((u, Eff::No))
            } else {
                Err(TypeError::InvalidSplit(e.clone(), s.clone(), s1.clone()))
            }
        }
        Expr::Inj(l, e1) => {
            // Assert that the type is a variant
            let cs = match &t.val {
                Type::Variant(cs) => cs,
                _ => {
                    return Err(TypeError::Mismatch(
                        e.clone(),
                        Err("Variant".to_owned()),
                        t.clone(),
                    ))
                }
            };
            // Assert that the variant contains the label
            let Some((_, t1)) = cs.iter().find(|(l2, _)| l.val == l2.val) else {
                return Err(TypeError::MismatchLabel(
                    e.clone(),
                    l.val.clone(),
                    t.clone(),
                ));
            };
            // Check the subexpression
            check(ctx, e1, t1)
        }
        _ => {
            let (t2, u, p) = infer(ctx, e)?;
            if t.val.eq(&t2.val) {
                Ok((u, p))
            } else {
                Err(TypeError::Mismatch(e.clone(), Ok(t.clone()), t2))
            }
        }
    }
}

pub fn infer(ctx: &Ctx, e: &SExpr) -> Result<(SType, Rep, Eff), TypeError> {
    match &e.val {
        Expr::Var(x) => match ctx.lookup_ord_pure(x) {
            Some((ctx, t)) => {
                assert_unr_ctx(e, &ctx)?;
                let u = match &t.val {
                    Type::Chan(s) => Rep::single(x.val.clone(), s.val.clone()),
                    _ => Rep::empty(),
                };
                Ok((t.clone(), u, Eff::No))
            }
            None => Err(TypeError::UndefinedVariable(x.clone())),
        },
        Expr::App(e1, e2) => {
            let fvs1 = e1.free_vars();
            let c1 = ctx.restrict(&fvs1);
            let (t1, u1, p1) = infer(&c1, e1)?;

            let Type::Arr(m, p, t11, t12) = &t1.val else {
                return Err(TypeError::Mismatch(
                    *e1.clone(),
                    Err("Function".into()),
                    t1.clone(),
                ));
            };

            if m.val == Mult::OrdR {
                return Err(TypeError::MismatchMult(
                    *e1.clone(),
                    t1.clone(),
                    Err("unr, lin, or left".into()),
                    m.clone(),
                ));
            }

            let fvs2 = e2.free_vars();
            let c2 = ctx.restrict(&fvs2).split_off(&u1);
            let (u2, p2) = check(&c2, e2, &t11)?;

            check_split_alg(e, &u1, &u2, &fvs1, &fvs2, ctx, &c1, &c2, m.to_join_ord())?;

            if m.val == Mult::OrdL && p2 == Eff::Yes {
                return Err(TypeError::MismatchEff(
                    *e2.clone(),
                    fake_span(Eff::No),
                    fake_span(Eff::Yes),
                ));
            }

            Ok((*t12.clone(), u1.join(&u2), Eff::lub(**p, Eff::lub(p1, p2))))
        }
        Expr::AppR(e1, e2) => {
            let fvs1 = e1.free_vars();
            let c1 = ctx.restrict(&fvs1);
            let (t1, u1, p1) = infer(&c1, e1)?;

            let fvs2 = e2.free_vars();
            let c2 = ctx.restrict(&fvs2).split_off(&u1);
            let (t2, u2, p2) = infer(&c2, e2)?;

            let Type::Arr(m, p, t11, t12) = &t2.val else {
                return Err(TypeError::Mismatch(
                    *e1.clone(),
                    Err("Function".into()),
                    t1.clone(),
                ));
            };
            if !t1.eq(t11) {
                return Err(TypeError::Mismatch(
                    *e1.clone(),
                    Ok(*t11.clone()),
                    t1.clone(),
                ));
            }

            if m.val != Mult::OrdR {
                return Err(TypeError::MismatchMult(
                    *e1.clone(),
                    t1.clone(),
                    Ok(fake_span(Mult::OrdR)),
                    m.clone(),
                ));
            }

            check_split_alg(e, &u1, &u2, &fvs1, &fvs2, ctx, &c1, &c2, m.to_join_ord())?;

            if p1 == Eff::Yes {
                return Err(TypeError::MismatchEff(
                    *e1.clone(),
                    fake_span(Eff::No),
                    fake_span(Eff::Yes),
                ));
            }

            Ok((*t12.clone(), u1.join(&u2), Eff::lub(**p, Eff::lub(p1, p2))))
        }
        Expr::Pair(e1, e2) => {
            let fvs1 = e1.free_vars();
            let c1 = ctx.restrict(&fvs1);
            let (t1, u1, p1) = infer(&c1, e1)?;

            let fvs2 = e2.free_vars();
            let c2 = ctx.restrict(&fvs2).split_off(&u1);
            let (t2, u2, p2) = infer(&c2, e2)?;

            let u = u1.join(&u2);

            let m = {
                let fvs: HashSet<Id> = fvs1.intersection(&fvs2).cloned().collect();
                let sis = split_infos(&fvs, &u1);
                let r1 = Ren::fresh_from(sis.keys(), "1");
                let r2 = Ren::fresh_from(sis.keys(), "2");
                let ctx_split = ctx.replace(&u).split_ctx(&sis, &r1, &r2);
                let c12_lin = CtxS::Join(
                    c1.replace(&u1).rename(&r1),
                    c2.replace(&u2).rename(&r2),
                    JoinOrd::Unordered,
                );
                if ctx_split.is_subctx_of(&c12_lin) {
                    Mult::Lin
                } else {
                    let c12_ordl = CtxS::Join(
                        c1.replace(&u1).rename(&r1),
                        c2.replace(&u2).rename(&r2),
                        JoinOrd::Ordered,
                    );
                    if ctx.is_subctx_of(&c12_ordl) {
                        Mult::OrdL
                    } else {
                        Err(TypeError::CtxSplitFailed(
                            e.clone(),
                            ctx_split.clone(),
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

            Ok((t_pair, u1.join(&u2), Eff::lub(p1, p2)))
        }
        Expr::Let(x, e1, e2) => {
            let fvs1 = e1.free_vars();
            let fvs2 = e2.free_vars();

            let c1 = ctx.restrict(&fvs1);
            let (t1, u1, p1) = infer(&c1, e1)?;

            let cc = compute_ctx_ctx(e, &u1, &fvs1, &fvs2, ctx)?;

            if cc.vars().contains(&x.val) {
                Err(TypeError::Shadowing(e.clone(), x.clone()))?
            }

            if !cc.is_left() && p1 == Eff::Yes {
                return Err(TypeError::MismatchEff(
                    *e1.clone(),
                    fake_span(Eff::No),
                    fake_span(Eff::Yes),
                ));
            }

            let c2 = cc.fill(Ctx::Bind(x.clone(), t1.clone()));
            let (t2, u2, p2) = infer(&c2, e2)?;

            // Assert that channel arguments are used up.
            if_chan_then_used(&e, &t1, &u2, &x)?;
            let u2 = u2.remove(&x);

            check_split_alg_gen(e, &u1, &u2, &fvs1, &fvs2, ctx, &c1, &cc)?;

            Ok((t2, u1.join(&u2), Eff::lub(p1, p2)))
        }
        Expr::Seq(e1, e2) => {
            let fvs1 = e1.free_vars();
            let fvs2 = e2.free_vars();

            let c1 = ctx.restrict(&fvs1);
            let (t1, u1, p1) = infer(&c1, e1)?;

            if t1.is_ord() {
                return Err(TypeError::SeqDropsOrd(e.clone(), t1.clone()));
            }

            let cc = compute_ctx_ctx(e, &u1, &fvs1, &fvs2, ctx)?;

            if !cc.is_left() && p1 == Eff::Yes {
                return Err(TypeError::MismatchEff(
                    *e1.clone(),
                    fake_span(Eff::No),
                    fake_span(Eff::Yes),
                ));
            }

            let c2 = cc.fill(Ctx::Empty);
            let (t2, u2, p2) = infer(&c2, e2)?;

            check_split_alg_gen(e, &u1, &u2, &fvs1, &fvs2, ctx, &c1, &cc)?;

            Ok((t2, u1.join(&u2), Eff::lub(p1, p2)))
        }
        Expr::LetPair(x, y, e1, e2) => {
            let fvs1 = e1.free_vars();
            let fvs2 = e2.free_vars();

            let c1 = ctx.restrict(&fvs1);
            let (t1, u1, p1) = infer(&c1, e1)?;

            let Type::Prod(m, t11, t12) = &t1.val else {
                return Err(TypeError::Mismatch(
                    *e1.clone(),
                    Err("Product".into()),
                    t1.clone(),
                ));
            };

            let cc = compute_ctx_ctx(e, &u1, &fvs1, &fvs2, ctx)?;

            if cc.vars().contains(&x.val) {
                Err(TypeError::Shadowing(e.clone(), x.clone()))?
            }
            if cc.vars().contains(&y.val) || x.val == y.val {
                Err(TypeError::Shadowing(e.clone(), y.clone()))?
            }

            if !cc.is_left() && p1 == Eff::Yes {
                return Err(TypeError::MismatchEff(
                    *e1.clone(),
                    fake_span(Eff::No),
                    fake_span(Eff::Yes),
                ));
            }

            let c2 = cc.fill(Ctx::Join(
                Box::new(Ctx::Bind(x.clone(), *t11.clone())),
                Box::new(Ctx::Bind(y.clone(), *t12.clone())),
                m.to_join_ord(),
            ));
            let (t2, u2, p2) = infer(&c2, e2)?;

            // Assert that channel arguments are used up.
            if_chan_then_used(&e, &t1, &u2, &x)?;
            if_chan_then_used(&e, &t2, &u2, &y)?;

            let u2 = u2.remove(&x).remove(&y);

            check_split_alg_gen(e, &u1, &u2, &fvs1, &fvs2, ctx, &c1, &cc)?;

            Ok((t2, u1.join(&u2), Eff::lub(p1, p2)))
        }
        Expr::CaseSum(e1, cs) => {
            let fvs1 = e1.free_vars();

            let c1 = ctx.restrict(&fvs1);
            let (t1, u1, p1) = infer(&c1, e1)?;

            let Type::Variant(tcs) = &t1.val else {
                return Err(TypeError::Mismatch(
                    *e1.clone(),
                    Err("Variant".into()),
                    t1.clone(),
                ));
            };

            let tls = tcs.iter().map(|(l, _)| &l.val).collect::<Vec<_>>();
            let ls = cs.iter().map(|(l, _x, _e)| &l.val).collect::<Vec<_>>();
            check_variant_label_eq(e, &t1, &ls, &tls)?;

            let e2s = cs.iter().map(|(_l, _x, e)| e).collect::<Vec<_>>();
            let fvs2 = union(e2s.iter().map(|e| e.free_vars()));
            let cc = compute_ctx_ctx(e, &u1, &fvs1, &fvs2, ctx)?;

            let xs = cs.iter().map(|(_l, x, _e)| x).collect::<Vec<_>>();
            for x in xs {
                if cc.vars().contains(&x.val) {
                    Err(TypeError::Shadowing(e.clone(), x.clone()))?
                }
            }

            if !cc.is_left() && p1 == Eff::Yes {
                return Err(TypeError::MismatchEff(
                    *e1.clone(),
                    fake_span(Eff::No),
                    fake_span(Eff::Yes),
                ));
            }

            let mut cs_zip = Vec::new();
            for (l, x, e) in cs {
                let (_, t) = tcs.iter().find(|(l2, _)| l.val == l2.val).unwrap();
                cs_zip.push((l, x, e, t));
            }

            let mut out: Option<(SType, Rep, Eff)> = None;
            for (_, x_, e_, t_) in &cs_zip {
                let c_ = cc.fill(Ctx::Bind((*x_).clone(), (*t_).clone()));
                let (t2_, u2_, p2_) = infer(&c_, e_)?;

                // Assert that channel arguments are used up.
                if_chan_then_used(&e_, &t2_, &u2_, &x_)?;

                if let Some((t2, u2, p2)) = &mut out {
                    if *t2 != t2_ {
                        return Err(TypeError::CaseClauseTypeMismatch(
                            e.clone(),
                            t2.clone(),
                            t2_.clone(),
                        ));
                    }
                    *p2 = Eff::lub(*p2, p2_);
                    check_rep_eq(&e, &u2, &u2_.remove(x_))?;
                } else {
                    out = Some((t2_, u2_.remove(x_), p2_))
                }
            }
            let (t2, u2, p2) = out.unwrap();

            check_split_alg_gen(e, &u1, &u2, &fvs1, &fvs2, ctx, &c1, &cc)?;

            Ok((t2, u1.join(&u2), Eff::lub(p1, p2)))
        }
        Expr::If(e1, e2, e3) => {
            let fvs1 = e1.free_vars();
            let fvs2 = union([e2.free_vars(), e3.free_vars()]);

            let c1 = ctx.restrict(&fvs1);
            let (u1, p1) = check(&c1, e1, &fake_span(Type::Bool))?;

            let cc = compute_ctx_ctx(e, &u1, &fvs1, &fvs2, ctx)?;

            if !cc.is_left() && p1 == Eff::Yes {
                return Err(TypeError::MismatchEff(
                    *e1.clone(),
                    fake_span(Eff::No),
                    fake_span(Eff::Yes),
                ));
            }

            let c2 = cc.fill(Ctx::Empty);
            let (t2, u2, p2) = infer(&c2, e2)?;
            let (t3, u3, p3) = infer(&c2, e3)?;

            if t2 != t3 {
                return Err(TypeError::CaseClauseTypeMismatch(
                    e.clone(),
                    t2.clone(),
                    t3.clone(),
                ));
            }
            check_rep_eq(&e, &u2, &u3)?;

            check_split_alg_gen(e, &u1, &u2, &fvs1, &fvs2, ctx, &c1, &cc)?;

            Ok((t2, u1.join(&u2), Eff::lub(p1, Eff::lub(p2, p3))))
        }
        Expr::Fork(e1) => {
            let (t, u, _p) = infer(ctx, e1)?;
            let Type::Unit = t.val else {
                return Err(TypeError::Mismatch(
                    *e1.clone(),
                    Err("Unit".into()),
                    t.clone(),
                ));
            };
            Ok((fake_span(Type::Unit), u, Eff::No))
        }
        Expr::New(s) => {
            assert_unr_ctx(&e, &ctx)?;
            let t = fake_span(Type::Prod(
                fake_span(Mult::OrdL),
                Box::new(fake_span(Type::Chan(fake_span(Session::Owned(s.clone()))))),
                Box::new(fake_span(Type::Chan(fake_span(Session::Owned(fake_span(
                    s.dual(),
                )))))),
            ));
            Ok((t, Rep::empty(), Eff::No))
        }
        Expr::Send(e1, e2) => {
            let fvs1 = e1.free_vars();
            let c1 = ctx.restrict(&fvs1);
            let (t1, u1, _p1) = infer(&c1, e1)?;

            let t2 = fake_span(Type::Chan(fake_span(Session::Borrowed(fake_span(
                SessionB::Op(
                    SessionOp::Send,
                    Box::new(t1.clone()),
                    Box::new(fake_span(SessionB::Return)),
                ),
            )))));

            let fvs2 = e2.free_vars();
            let c2 = ctx.restrict(&fvs2).split_off(&u1);
            let (u2, _p2) = check(&c2, e2, &t2)?;

            check_split_alg(e, &u1, &u2, &fvs1, &fvs2, ctx, &c1, &c2, JoinOrd::Unordered)?;

            Ok((fake_span(Type::Unit), u1.join(&u2), Eff::Yes))
        }
        Expr::Recv(e1) => {
            let (t, u, _p) = infer(ctx, e1)?;

            let err = Err(TypeError::Mismatch(
                *e1.clone(),
                Err(format!("Chan ?t.return  (for some type t)")),
                t.clone(),
            ));
            let Type::Chan(s) = t.val else {
                return err;
            };
            let Session::Borrowed(s) = s.val else {
                return err;
            };
            let SessionB::Op(SessionOp::Recv, t, s) = s.val else {
                return err;
            };
            let SessionB::Return = s.val else {
                return err;
            };

            Ok((*t, u, Eff::Yes))
        }
        Expr::Drop(e1) => {
            let (t, u, _p) = infer(ctx, e1)?;

            let err = Err(TypeError::Mismatch(
                *e1.clone(),
                Err(format!("Chan return")),
                t.clone(),
            ));
            let Type::Chan(s) = t.val else {
                return err;
            };
            let Session::Borrowed(s) = s.val else {
                return err;
            };
            let SessionB::Return = s.val else {
                return err;
            };

            Ok((fake_span(Type::Unit), u, Eff::Yes))
        }
        Expr::End(op, e1) => {
            let (t, u, _p) = infer(ctx, e1)?;

            let err = Err(TypeError::Mismatch(
                *e1.clone(),
                if *op == SessionOp::Send {
                    Err(format!("Chan term"))
                } else {
                    Err(format!("Chan wait"))
                },
                t.clone(),
            ));
            let Type::Chan(s) = t.val else {
                return err;
            };
            let Session::Owned(s) = s.val else {
                return err;
            };
            if s.val != SessionO::End(*op) {
                return err;
            }

            Ok((fake_span(Type::Unit), u, Eff::Yes))
        }
        Expr::Const(c) => {
            assert_unr_ctx(&e, &ctx)?;
            Ok((fake_span(c.type_()), Rep::empty(), Eff::No))
        }
        Expr::Ann(e, t) => {
            let (u, eff) = check(ctx, e, t)?;
            Ok((t.clone(), u, eff))
        }

        Expr::Abs(_x, _e1) => Err(TypeError::TypeAnnotationMissing(e.clone())),
        Expr::Borrow(_x) => Err(TypeError::TypeAnnotationMissing(e.clone())),
        Expr::Inj(_l, _e1) => Err(TypeError::TypeAnnotationMissing(e.clone())),
        Expr::Op1(op1, e1) => {
            let (t1, u1, p1) = infer(ctx, e1)?;
            let t = match (op1, &t1.val) {
                (Op1::Neg, Type::Int) => Type::Int,
                (Op1::Neg, _) => {
                    return Err(TypeError::Mismatch(
                        e.clone(),
                        Err(format!("Int")),
                        t1.clone(),
                    ))
                }
                (Op1::Not, Type::Bool) => Type::Bool,
                (Op1::Not, _) => {
                    return Err(TypeError::Mismatch(
                        e.clone(),
                        Err(format!("Bool")),
                        t1.clone(),
                    ))
                }
                (Op1::ToStr, _) => Type::String,
                (Op1::Print, _) => Type::Unit,
            };
            Ok((fake_span(t), u1, p1))
        }
        Expr::Op2(op2, e1, e2) => {
            let fvs1 = e1.free_vars();
            let c1 = ctx.restrict(&fvs1);
            let (t1, u1, p1) = infer(&c1, e1)?;

            let fvs2 = e2.free_vars();
            let c2 = ctx.restrict(&fvs2).split_off(&u1);
            let (t2, u2, p2) = infer(&c2, e2)?;

            let t = match (op2, &t1.val, &t2.val) {
                (Op2::Add, Type::Int, Type::Int) => Type::Int,
                (Op2::Add, Type::String, Type::String) => Type::String,
                (Op2::Add, _, _) => {
                    return Err(TypeError::Op2Mismatch(
                        e.clone(),
                        Err(format!("String or Int")),
                        t1.clone(),
                        t2.clone(),
                    ))
                }
                (Op2::Sub | Op2::Mul | Op2::Div, Type::Int, Type::Int) => Type::Int,
                (Op2::Sub | Op2::Mul | Op2::Div, _, _) => {
                    return Err(TypeError::Op2Mismatch(
                        e.clone(),
                        Err(format!("Int")),
                        t1.clone(),
                        t2.clone(),
                    ))
                }
                (
                    Op2::Eq | Op2::Neq | Op2::Lt | Op2::Le | Op2::Gt | Op2::Ge,
                    t1 @ (Type::Int | Type::Bool | Type::String | Type::Unit),
                    t2,
                ) if t1 == t2 => Type::Bool,
                (Op2::Eq | Op2::Neq | Op2::Lt | Op2::Le | Op2::Gt | Op2::Ge, _, _) => {
                    return Err(TypeError::Op2Mismatch(
                        e.clone(),
                        Err(format!("Int or Bool or String or Unit")),
                        t1.clone(),
                        t2.clone(),
                    ))
                }
                (Op2::And | Op2::Or, Type::Bool, Type::Bool) => Type::Bool,
                (Op2::And | Op2::Or, _, _) => {
                    return Err(TypeError::Op2Mismatch(
                        e.clone(),
                        Err(format!("Bool")),
                        t1.clone(),
                        t2.clone(),
                    ))
                }
            };

            check_split_alg(e, &u1, &u2, &fvs1, &fvs2, ctx, &c1, &c2, JoinOrd::Ordered)?;

            Ok((fake_span(t), u1.join(&u2), Eff::lub(p1, p2)))
        }
        Expr::LetDecl(x, t, cs, e2) => {
            let c: &SClause = if cs.len() == 1 {
                cs.first().unwrap()
            } else {
                return Err(TypeError::MultipleClauses(e.clone()));
            };
            if c.id.val != x.val {
                Err(TypeError::ClauseWithWrongId(
                    e.clone(),
                    c.id.clone(),
                    x.clone(),
                ))?
            }

            let (arg_tys, ret_ty, ret_eff) = split_arrow_type(t);
            //let ret_eff = if let Some(ret_eff) = ret_eff {
            //    ret_eff
            //} else {
            //    Err(TypeError::ClauseWithZeroPatterns(e.clone()))?
            //};
            if c.pats.len() != arg_tys.len() {
                Err(TypeError::NotEnoughPatterns(e.clone()))?
            }

            let fvs1 = c.free_vars();
            let c1 = ctx.restrict(&fvs1);
            let mut ctx_body = c1.clone();
            let all_unr = arg_tys.iter().all(|(_t, m)| m.val == Mult::Unr);
            if c.pats.len() > 0 && all_unr {
                ctx_body = ext(Mult::Unr, ctx_body, Ctx::Bind(x.clone(), t.clone()));
            } else {
                if fvs1.contains(&x.val) {
                    Err(TypeError::RecursiveNonFunctionBinding(e.clone(), x.clone()))?
                }
            }
            for (pat, (arg_ty, m)) in c.pats.iter().zip(arg_tys) {
                ctx_body = ext(m.val, ctx_body, check_pattern(pat, &arg_ty)?);
            }
            let (mut u1, mut p1) = check(&ctx_body, &c.val.body, &ret_ty)?;
            if let Some(ret_eff) = ret_eff {
                if !Eff::leq(p1, ret_eff.val) {
                    Err(TypeError::MismatchEffSub(e.clone(), fake_span(p1), ret_eff))?
                }
            }
            for p in &c.pats {
                for x in p.bound_vars() {
                    u1 = u1.remove(&x);
                }
            }
            if c.pats.len() != 0 {
                p1 = Eff::No
            }

            //let ctx = CtxS::Join(CtxS::Bind(x.clone(), t.clone()), ctx, JoinOrd::Ordered);
            //infer(&ctx, e2);
            //    }

            let cc = compute_ctx_ctx(e, &u1, &fvs1, &e2.free_vars(), ctx)?;

            if cc.vars().contains(&x.val) {
                Err(TypeError::Shadowing(e.clone(), x.clone()))?
            }

            if !cc.is_left() && p1 == Eff::Yes {
                return Err(TypeError::MismatchEff(
                    e.clone(), // TODO
                    fake_span(Eff::No),
                    fake_span(Eff::Yes),
                ));
            }

            let c2 = cc.fill(Ctx::Bind(x.clone(), t.clone()));
            let (t2, u2, p2) = infer(&c2, e2)?;

            // Assert that channel arguments are used up.
            if_chan_then_used(&e, &t, &u2, &x)?;
            let u2 = u2.remove(&x);

            check_split_alg_gen(e, &u1, &u2, &fvs1, &e2.free_vars(), ctx, &c1, &cc)?;

            Ok((t2, u1.join(&u2), Eff::lub(p1, p2)))
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
    let (t, u, eff) = infer(&Ctx::Empty, e)?;
    Ok((t, eff))
}

pub fn assert_unr_ctx(e: &SExpr, ctx: &Ctx) -> Result<(), TypeError> {
    if ctx.is_unr() {
        Ok(())
    } else {
        Err(TypeError::LeftOverCtx(e.clone(), ctx.clone()))
    }
}
