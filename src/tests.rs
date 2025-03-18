use crate::{
    error_reporting::{report_error, IErr},
    syntax::{Eff, SExpr, Type},
    typecheck,
};

pub fn typecheck_(src: &str) -> Result<(SExpr, Type, Eff), IErr> {
    typecheck(src, false).map_err(|e| {
        report_error("<nofile>", &src, e.clone());
        e
    })
}

#[test]
fn ty_id_unr_ann() {
    let src = "λ[unr] x. x : Unit -[ unr; 0 ]→ Unit";
    // let src = "λ[unr] x. x : Unit -[u0]→ Unit";
    // let src = "λ[unr] x. x : Unit -[u;0]→ Unit";
    // let src = "λ[unr] x. x : Unit →u0 Unit";
    assert!(typecheck_(src).is_ok());
}

#[test]
fn ty_id_unr() {
    let src = "λx. x : Unit –[u 0]→ Unit";
    assert!(typecheck_(src).is_ok());
}

#[test]
fn ty_res_simple() {
    let src = "drop (!{x} (new {x})) : Unit";
    assert!(typecheck_(src).is_ok());
}

#[test]
fn ty_res_let() {
    let src = "let x, y = split {a} (new {ab}) in drop (!{a} x); drop (!{b} y) : Unit";
    assert!(typecheck_(src).is_ok());
}

// FIXME: this should fail
#[test]
fn ty_fail_throwaway() {
    let src = "let r = new {xy} in unit";
    assert!(typecheck_(src).is_err());
}

#[test]
fn ty_borrow_desugared() {
    let src = "
let f = λc. drop (!{x} c) : {x} -[ unr; 1 ]→ Unit in
let r = new {xy} in
let r1, r2 = split {x} r in
f r1;
drop (!{y} r2)
";
    assert!(typecheck_(src).is_ok());
}

// #[test]
// fn ty_borrow() {
//     let src = "
// let f = λc. drop (!{x} c) : {x} -[ unr; 1 ]→ Unit in
// let r = new {xy} in
// f & r;
// drop (!{y} r)
// ";
//     assert!(typecheck_(src).is_ok());
// }
