use crate::util::pretty::{Assoc, Pretty, PrettyEnv};

use super::regex::Regex;

use Assoc::Left as L;
use Assoc::Right as R;

pub struct Char<C>(C);

impl Pretty<()> for Char<char> {
    fn pp(&self, p: &mut PrettyEnv<()>) {
        p.pp(self);
    }
}

impl Pretty<()> for Char<u8> {
    fn pp(&self, p: &mut PrettyEnv<()>) {
        if let Some(c) = char::from_u32(self.0 as u32) {
            p.pp(&c.to_string())
        } else {
            p.pp(&format!("<{}>", self.0))
        }
    }
}

impl<C: Copy> Pretty<()> for Regex<C>
where
    Char<C>: Pretty<()>,
{
    fn pp(&self, p: &mut PrettyEnv<()>) {
        match self {
            Regex::Empty => p.pp("∅"),
            Regex::Eps => p.pp("ε"),
            Regex::Char(c) => p.pp(&Char(*c)),
            Regex::Or(e1, e2) => p.infix(1, L, |p| {
                p.pp_arg(L, e1);
                p.pp("|");
                p.pp_arg(R, e2);
            }),
            Regex::And(e1, e2) => p.infix(2, L, |p| {
                p.pp_arg(L, e1);
                p.pp("&");
                p.pp_arg(R, e2);
            }),
            Regex::Seq(e1, e2) => p.infix(3, L, |p| {
                p.pp_arg(L, e1);
                p.pp_arg(R, e2);
            }),
            Regex::Star(e) => p.infix(4, L, |p| {
                p.pp_arg(L, e);
                p.pp("*");
            }),
            Regex::Neg(e) => p.infix(4, L, |p| {
                p.pp("¬");
                p.pp_arg(L, e);
            }),
        }
    }
}
