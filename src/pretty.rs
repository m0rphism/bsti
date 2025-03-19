use crate::{
    syntax::{
        Clause, Const, Eff, Expr, Mult, Op1, Op2, Pattern, SMult, Session, SessionB, SessionO,
        SessionOp, Type,
    },
    util::{
        pretty::{Assoc, Pretty, PrettyEnv},
        span::Spanned,
    },
};

// #[derive(Clone)]
// pub struct UserState {}
type UserState = ();

use Assoc::Left as L;
use Assoc::None as N;
use Assoc::Right as R;

impl<T: Pretty<UserState>> Pretty<UserState> for Spanned<T> {
    fn pp(&self, p: &mut PrettyEnv<UserState>) {
        self.val.pp(p)
    }
}

impl Pretty<UserState> for Type {
    fn pp(&self, p: &mut PrettyEnv<UserState>) {
        match self {
            Type::Arr(m, e, t1, t2) => p.infix(2, R, |p| {
                p.pp_arg(L, t1);
                p.pp(" –[");
                p.pp(m);
                p.pp("; ");
                p.pp(e);
                p.pp("]→ ");
                p.pp_arg(R, t2);
            }),
            Type::Prod(m, t1, t2) => p.infix(3, N, |p| {
                p.pp_arg(L, t1);
                match m.val {
                    Mult::Lin => {
                        p.pp(" ⊗ ");
                    }
                    Mult::OrdL => {
                        p.pp(" ⊙ ");
                    }
                    _ => {
                        p.pp(" *[");
                        p.pp(m);
                        p.pp("] ");
                    }
                }
                p.pp_arg(R, t2);
            }),
            Type::Chan(s) => p.infix(4, N, |p| {
                p.pp("Chan ");
                p.pp_arg(R, s);
            }),
            Type::Variant(cs) => {
                p.pp("<");
                for (i, (l, t)) in cs.iter().enumerate() {
                    if i != 0 {
                        p.pp(", ");
                    }
                    p.pp(l);
                    p.pp(": ");
                    p.pp_prec(0, t);
                }
                p.pp(">");
            }
            Type::Unit => p.pp("Unit"),
            Type::Int => p.pp("Int"),
            Type::Bool => p.pp("Bool"),
            Type::String => p.pp("String"),
        }
    }
}

impl Pretty<UserState> for Session {
    fn pp(&self, p: &mut PrettyEnv<UserState>) {
        match self {
            Session::Owned(s) => p.pp(s),
            Session::Borrowed(s) => p.pp(s),
        }
    }
}

impl Pretty<UserState> for SessionO {
    fn pp(&self, p: &mut PrettyEnv<UserState>) {
        match self {
            SessionO::Op(op, t, s) => p.infix(0, R, |p| {
                match op {
                    SessionOp::Send => p.pp("!"),
                    SessionOp::Recv => p.pp("?"),
                }
                p.pp_prec(10, t);
                p.pp(". ");
                p.pp(s);
            }),
            SessionO::End(op) => match op {
                SessionOp::Send => p.pp("term"),
                SessionOp::Recv => p.pp("wait"),
            },
        }
    }
}

impl Pretty<UserState> for SessionB {
    fn pp(&self, p: &mut PrettyEnv<UserState>) {
        match self {
            SessionB::Op(op, t, s) => p.infix(0, R, |p| {
                match op {
                    SessionOp::Send => p.pp("!"),
                    SessionOp::Recv => p.pp("?"),
                }
                p.pp_prec(10, t);
                p.pp(". ");
                p.pp(s);
            }),
            SessionB::Return => p.pp("return"),
        }
    }
}

impl Pretty<UserState> for Mult {
    fn pp(&self, p: &mut PrettyEnv<UserState>) {
        match self {
            Mult::Unr => p.pp("unr"),
            Mult::Lin => p.pp("lin"),
            Mult::OrdL => p.pp("left"),
            Mult::OrdR => p.pp("right"),
        }
    }
}

impl Pretty<UserState> for Option<SMult> {
    fn pp(&self, p: &mut PrettyEnv<UserState>) {
        match self {
            None => (),
            Some(m) => {
                p.pp("[");
                p.pp(m);
                p.pp("]");
            }
        }
    }
}

impl Pretty<UserState> for Eff {
    fn pp(&self, p: &mut PrettyEnv<UserState>) {
        match self {
            Eff::Yes => p.pp("1"),
            Eff::No => p.pp("0"),
        }
    }
}

impl Pretty<UserState> for Expr {
    fn pp(&self, p: &mut PrettyEnv<UserState>) {
        match self {
            Expr::New(r) => p.infix(3, L, |p| {
                p.pp("new {");
                p.pp_prec(0, r);
                p.pp("}")
            }),
            Expr::Drop(e) => p.infix(2, L, |p| {
                p.pp("drop ");
                p.pp_arg(R, e);
            }),
            Expr::Var(x) => p.str(&x.val),
            Expr::Abs(x, e) => p.infix(1, R, |p| {
                p.pp("λ");
                p.pp(x);
                p.pp(". ");
                p.pp_arg(R, e);
                p.pp("");
            }),
            Expr::App(e1, e2) => p.infix(10, L, |p| {
                p.pp_arg(L, e1);
                p.pp(" ");
                p.pp_arg(R, e2);
            }),
            Expr::AppR(e1, e2) => p.infix(10, L, |p| {
                p.pp_arg(L, e1);
                p.pp(" |> ");
                p.pp_arg(R, e2);
            }),
            Expr::Inj(l, e) => p.infix(10, L, |p| {
                p.pp("inj ");
                p.pp(l);
                p.pp(" ");
                p.pp_arg(R, e);
            }),
            Expr::Fork(e) => p.infix(10, L, |p| {
                p.pp("fork ");
                p.pp_arg(R, e);
            }),
            Expr::Send(e1, e2) => p.infix(10, L, |p| {
                p.pp("send ");
                p.pp_arg(R, e1);
                p.pp(" ");
                p.pp_arg(R, e2);
            }),
            Expr::Recv(e) => p.infix(10, L, |p| {
                p.pp("recv ");
                p.pp_arg(R, e);
            }),
            Expr::End(op, e) => p.infix(10, L, |p| {
                match op {
                    SessionOp::Send => p.pp("term"),
                    SessionOp::Recv => p.pp("wait"),
                }
                p.pp(" ");
                p.pp_arg(R, e);
            }),
            Expr::Pair(e1, e2) => {
                p.pp("(");
                p.pp(e1);
                p.pp(", ");
                p.pp(e2);
                p.pp(")");
            }
            Expr::LetPair(x, y, e1, e2) => p.infix(1, R, |p| {
                p.pp("let ");
                p.pp(x);
                p.pp(", ");
                p.pp(y);
                p.pp(" = ");
                p.pp(e1);
                p.pp(" in ");
                p.pp(e2);
            }),
            Expr::Let(x, e1, e2) => p.infix(1, R, |p| {
                p.pp("let ");
                p.pp(x);
                p.pp(" = ");
                p.pp(e1);
                p.pp(" in ");
                p.pp(e2);
            }),
            Expr::CaseSum(e, cs) => p.infix(1, R, |p| {
                p.pp("case ");
                p.pp(e);
                p.pp(" { ");
                for (l, x, e) in cs {
                    p.pp("inj ");
                    p.pp(l);
                    p.pp(" ");
                    p.pp(x);
                    p.pp(" → ");
                    p.pp_prec(0, e);
                }
                p.pp(" }");
            }),
            Expr::Ann(e, t) => {
                p.pp(e);
                p.pp(" : ");
                p.pp(t);
            }
            Expr::Seq(e1, e2) => p.infix(2, R, |p| {
                p.pp_arg(L, e1);
                p.pp("; ");
                p.pp_arg(R, e2);
            }),
            Expr::LetDecl(x, t, cs, e) => {
                p.pp(x);
                p.pp(" : ");
                p.pp(t);
                p.pp("\n");
                for c in cs {
                    p.pp(c);
                }
                p.pp("\n");
                p.pp(e)
            }
            Expr::Borrow(x) => {
                p.pp("&");
                p.pp(x);
            }
            Expr::Const(Const::Unit) => p.pp("unit"),
            Expr::Const(Const::Int(v)) => p.pp(&v.to_string()),
            Expr::Const(Const::Bool(v)) => p.pp(&v.to_string()),
            Expr::Const(Const::String(v)) => p.pp(&format!("\"{v}\"")),
            Expr::Op1(op1, e) => {
                let (prec, assoc, op_str) = match op1 {
                    Op1::Neg => (9, N, "!"),
                    Op1::Not => (6, N, "!"),
                    Op1::ToStr => (10, N, "str"),
                    Op1::Print => (10, N, "print"),
                };
                p.infix(prec, assoc, |p| {
                    p.pp(op_str);
                    p.pp(" ");
                    p.pp_arg(R, e);
                })
            }
            Expr::Op2(op2, e1, e2) => {
                let (prec, assoc, op_str) = match op2 {
                    Op2::Add => (8, L, "+"),
                    Op2::Sub => (8, L, "-"),
                    Op2::Mul => (9, R, "*"),
                    Op2::Div => (9, R, "/"),
                    Op2::Eq => (7, N, "=="),
                    Op2::Neq => (7, N, "!="),
                    Op2::Lt => (7, N, "<"),
                    Op2::Le => (7, N, "<="),
                    Op2::Gt => (7, N, ">"),
                    Op2::Ge => (7, N, ">="),
                    Op2::And => (5, L, "&&"),
                    Op2::Or => (4, L, "||"),
                };
                p.infix(prec, assoc, |p| {
                    p.pp_arg(L, e1);
                    p.pp(" ");
                    p.pp(op_str);
                    p.pp(" ");
                    p.pp_arg(R, e2);
                })
            }
        }
    }
}

impl Pretty<UserState> for Clause {
    fn pp(&self, p: &mut PrettyEnv<UserState>) {
        p.pp(&self.id);
        p.pp(" ");
        for pat in &self.pats {
            p.pp(pat);
            p.pp(" ");
        }
        p.pp("= ");
        p.pp(&self.body);
        p.pp("\n")
    }
}

impl Pretty<UserState> for Pattern {
    fn pp(&self, p: &mut PrettyEnv<UserState>) {
        match self {
            Pattern::Var(x) => p.pp(x),
            Pattern::Pair(p1, p2) => {
                p.pp("(");
                p.pp(p1);
                p.pp(", ");
                p.pp(p2);
                p.pp(")");
            }
            Pattern::Inj(sum_label, spanned) => todo!(),
        }
    }
}

//     Expr::Int(x) => p.str(format!("{x}")),
//     Expr::Float(x) => p.str(format!("{x}")),
//     Expr::String(x) => p.str(format!("\"{x}\"")), // TODO: escaping
//     Expr::Bool(true) => p.str("True"),
//     Expr::Bool(false) => p.str("False"),
//     Expr::List(es) => {
//         p.pp("[");
//         p.pp_sep(", ", es);
//         p.pp("]");
//     }
//     Expr::ListAccess(e1, e2) => {
//         p.pp(e1);
//         p.pp("[");
//         p.pp(e2);
//         p.pp("]");
//     }
//     Expr::Binop(op, e1, e2) => {
//         p.pp(e1);
//         p.pp(" ");
//         p.pp(op);
//         p.pp(" ");
//         p.pp(e2);
//     }
//     Expr::Unop(op, e) => {
//         p.pp(op);
//         p.pp(" ");
//         p.pp(e);
//     }
//     Expr::Scope(prog) => {
//         p.block_inline(|p| {
//             p.pp("{{");
//             p.user_state.stack.push(prog.frame.clone());
//             p.block(|p| {
//                 p.pp(prog);
//             });
//             p.user_state.stack.pop();
//             p.nl();
//             p.pp("}}");
//         });
//     }
//     Expr::None => p.pp("None"),
//     Expr::Loc(l) => {
//         if p.user_state.implicit_heap && !p.user_state.in_heap {
//             match p.user_state.heap.lookup(*l) {
//                 Ok(v) => {
//                     let annotate = !p.user_state.implicit_heap_only_duplicates
//                         || p.user_state.heap.contains_value_not_at(v, *l)
//                         || !p.user_state.stack.is_unique_value(&Expr::Loc(*l));
//                     if annotate {
//                         p.pp(&format!("{}:", l));
//                     }
//                     p.pp(v);
//                 }
//                 Err(e) => p.pp(&format!("<{}:{}>", l, e)),
//             }
//         } else {
//             p.pp(&format!("<{}>", l))
//         }
//     }

// impl<'a> Pretty<UserState> for Binop {
//     fn pp(&self, p: &mut PrettyEnv<UserState>) {
//         match self {
//             Binop::Add => p.str("+"),
//             Binop::Mul => p.str("*"),
//             Binop::Sub => p.str("-"),
//             Binop::Div => p.str("/"),
//             Binop::And => p.str("and"),
//             Binop::Or => p.str("or"),
//             Binop::Lt => p.str("<"),
//             Binop::Le => p.str("<="),
//             Binop::Gt => p.str(">"),
//             Binop::Ge => p.str(">="),
//             Binop::Eq => p.str("=="),
//             Binop::Neq => p.str("!="),
//         }
//     }
// }

// impl<'a> Pretty<UserState> for Unop {
//     fn pp(&self, p: &mut PrettyEnv<UserState>) {
//         match self {
//             Unop::Not => p.str("not"),
//             Unop::Neg => p.str("-"),
//         }
//     }
// }
