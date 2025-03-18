use crate::{
    syntax::{Clause, Eff, Expr, Mult, Pattern, SMult, Type},
    util::pretty::{Assoc, Pretty, PrettyEnv},
    util::span::Spanned,
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
            Type::Unit => p.pp("Unit"),
            Type::Regex(r) => {
                p.pp("{");
                p.pp_prec(0, r);
                p.pp("}");
            }
            Type::Arr(m, e, t1, t2) => p.infix(2, R, |p| {
                p.pp_arg(L, t1);
                p.pp(" –[");
                p.pp(m);
                p.pp("; ");
                p.pp(e);
                p.pp("]→ ");
                p.pp_arg(R, t2);
            }),
            Type::Prod(m, t1, t2) => p.infix(2, N, |p| {
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

// impl Pretty<UserState> for Regex {
//     fn pp(&self, p: &mut PrettyEnv<UserState>) {
//         p.pp("<");
//         p.pp(self);
//         p.pp(">");
//     }
// }

// impl Pretty<UserState> for Word {
//     fn pp(&self, p: &mut PrettyEnv<UserState>) {
//         p
//     }
// }

impl Pretty<UserState> for Expr {
    fn pp(&self, p: &mut PrettyEnv<UserState>) {
        match self {
            Expr::Unit => p.pp("unit"),
            Expr::New(r) => p.infix(3, L, |p| {
                p.pp("new {");
                p.pp_prec(0, r);
                p.pp("}")
            }),
            Expr::Write(w, e) => p.infix(3, L, |p| {
                p.pp("!{");
                p.pp(w);
                p.pp("} ");
                p.pp_arg(R, e);
            }),
            Expr::Split(r, e) => p.infix(3, L, |p| {
                p.pp("split ");
                p.pp(r);
                p.pp(" ");
                p.pp_arg(R, e);
            }),
            Expr::Drop(e) => p.infix(2, L, |p| {
                p.pp("drop ");
                p.pp_arg(R, e);
            }),
            Expr::Var(x) => p.str(&x.val),
            Expr::Abs(om, x, e) => p.infix(1, R, |p| {
                p.pp("λ");
                p.pp(om);
                p.pp(x);
                p.pp(". ");
                p.pp_arg(R, e);
                p.pp("");
            }),
            Expr::App(om, e1, e2) => p.infix(3, L, |p| {
                p.pp_arg(L, e1);
                p.pp(" ");
                if let Some(m) = om {
                    p.pp("[");
                    p.pp(m);
                    p.pp("] ");
                }
                p.pp_arg(R, e2);
            }),
            Expr::AppBorrow(e1, e2) => p.infix(3, L, |p| {
                p.pp_arg(L, e1);
                p.pp(" &");
                p.pp_arg(R, e2);
            }),
            Expr::Loc(l) => {
                p.pp(&format!("#{l:?}"));
            }
            Expr::Pair(om, e1, e2) => {
                p.pp("(");
                p.pp(e1);
                p.pp(",");
                p.pp(om);
                p.pp(" ");
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
