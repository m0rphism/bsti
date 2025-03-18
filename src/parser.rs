use crate::lexer::Token;
use crate::regex::parser::regex_parser;
use crate::regex::Regex as RegexS;
use crate::syntax::Eff as EffS;
use crate::syntax::Id as IdS;
use crate::syntax::*;
use crate::util::lexer_offside::Braced;
use crate::util::peg_logos::SpannedToks;
use crate::util::span::fake_span;
use crate::util::span::{Span, Spanned};

use peg::error::ParseError;
use Braced::Token as Tok;

pub type Toks<'a> = SpannedToks<'a, Braced<Token<'a>>>;

pub fn parse(toks: &Toks) -> Result<SExpr, ParseError<usize>> {
    rlang_parser::sprogram(toks, toks)
}

#[cfg_attr(rustfmt, rustfmt_skip)]
peg::parser! {
    pub grammar rlang_parser<'a>(toks: &'a Toks<'a>) for Toks<'a> {
        use Token::*;

        rule spanned<T>(t: rule<T>) -> Spanned<T>
            = start:position!() x:t() end:position!() {
                // TODO: For some reason the position reporting in `peg_logos` doesn't work,
                // so we use this workaround to convert token-spans to byte-spans ourself...
                let start = toks.toks.get(start)
                        .map(|t| t.span.start)
                        .unwrap_or_else(|| toks.toks.last().unwrap().span.end);
                let end = if end > 0 { end - 1 } else { end };
                let end = toks.toks.get(end)
                        .map(|t| t.span.end)
                        .unwrap_or_else(|| toks.toks.last().unwrap().span.end);
                Spanned::new(x, Span { start, end })
            }

        // Identifier

        pub rule id() -> IdS = quiet!{[Tok(Id(x))] { x.to_owned() }} / expected!("identifier")
        pub rule sid() -> SId = spanned(<id()>)

        pub rule tok(t: Token<'a>) -> () = quiet!{[Tok(t2) if t == t2] { () }} / expected!(t.to_str())

        // Multiplicities

        pub rule mult() -> Mult
            = (tok(Unr) / [Tok(Id("u"))]) { Mult::Unr }
            / (tok(Lin) / [Tok(Id("p"))]) { Mult::Lin }
            / (tok(Left) / [Tok(Id("l"))]) { Mult::OrdL }
            / (tok(Right) / [Tok(Id("r"))]) { Mult::OrdR }
            / expected!("multiplicity")
        pub rule smult() -> SMult = spanned(<mult()>)

        // Effects

        pub rule effect() -> EffS
            = quiet!{[Tok(Int(0))] { EffS::No }}
            / quiet!{[Tok(Int(1))] { EffS::Yes }}
            / expected!("effect")
        pub rule seffect() -> SEff = spanned(<effect()>)

        // Types

        pub rule type_() -> Type = t:type_arrow() { t }
        pub rule stype() -> SType = spanned(<type_()>)

        #[cache_left_rec]
        pub rule type_arrow() -> Type
            = t1:stype_prod() tok(Minus) tok(BracketL) m:smult() tok(Semicolon)? e:seffect()
              tok(BracketR) tok(Arrow) t2:stype_arrow()
              { Type::Arr(m, e, Box::new(t1), Box::new(t2)) }
            / t:type_prod() { t }
        pub rule stype_arrow() -> SType = spanned(<type_arrow()>)

        pub rule type_prod() -> Type
            = t1:stype_atom() tok(Star) tok(BracketL) m:smult() tok(BracketR) t2:stype_prod()
              { Type::Prod(m, Box::new(t1), Box::new(t2)) }
            / t1:stype_atom() tok(StarOrdL) t2:stype_prod()
              { Type::Prod(fake_span(Mult::OrdL), Box::new(t1), Box::new(t2)) }
            / t1:stype_atom() tok(StarLin) t2:stype_prod()
              { Type::Prod(fake_span(Mult::Lin), Box::new(t1), Box::new(t2)) }
            / t:type_atom() { t }
         
        pub rule stype_prod() -> SType = spanned(<type_prod()>)

        pub rule type_atom() -> Type
            = tok(UnitT) { Type::Unit }
            / tok(ParenL) t:type_() tok(ParenR) { t }
            / r:sregex() { Type::Regex(r) }
        pub rule stype_atom() -> SType = spanned(<type_atom()>)

        // Expressions

        pub rule expr() -> Expr = e:expr_ann() { e }
        pub rule sexpr() -> SExpr = spanned(<expr()>)

        pub rule expr_ann() -> Expr
            = e:sexpr_lam() tok(Colon) t:stype() { Expr::Ann(Box::new(e), t) }
            / e:expr_lam() { e }
        pub rule sexpr_ann() -> SExpr = spanned(<expr_ann()>)

        pub rule smult_opt() -> Option<SMult>
            = om:(tok(BracketL) m:smult() tok(BracketR) { m })? { om }

        #[cache]
        pub rule expr_lam() -> Expr
            = tok(Lambda) m:smult_opt() x:sid() tok(Period) e:sexpr_lam()
              { Expr::Abs(m, x, Box::new(e)) }
            / tok(Let) x:sid() tok(Comma) y:sid() tok(Equals) e1:sexpr_ann() tok(In) e2:sexpr_lam()
              { Expr::LetPair(x, y, Box::new(e1), Box::new(e2)) }
            / tok(Let) x:sid() tok(Equals) e1:sexpr_ann() tok(In) e2:sexpr_lam()
              { Expr::Let(x, Box::new(e1), Box::new(e2)) }
            / tok(Let) x:sid() tok(Colon) t:stype() cs:sclause()* tok(In) e:sexpr_lam()
              { Expr::LetDecl(x, t, cs, Box::new(e)) }
            / e:expr_seq() { e }
        pub rule sexpr_lam() -> SExpr = spanned(<expr_lam()>)

        #[cache_left_rec]
        pub rule expr_seq() -> Expr
            = e1:sexpr_app() tok(Semicolon) e2:sexpr_seq() { Expr::Seq(Box::new(e1), Box::new(e2)) }
            / e:expr_app() { e }
        pub rule sexpr_seq() -> SExpr = spanned(<expr_seq()>)

        #[cache_left_rec]
        pub rule expr_app() -> Expr
            = tok(New) r:sregex() { Expr::New(r) }
            / tok(Bang) w:sregex() e:sexpr_atom() { Expr::Write(w, Box::new(e)) }
            / tok(Split) r:sregex() e:sexpr_atom() { Expr::Split(r, Box::new(e)) }
            / tok(Drop) e:sexpr_atom() { Expr::Drop(Box::new(e)) }
            / e1:sexpr_app() tok(Amp) x:sid() { Expr::AppBorrow(Box::new(e1), x) }
            / e1:sexpr_app() e2:sexpr_atom() { Expr::App(None, Box::new(e1), Box::new(e2)) }
            / e:expr_atom() { e }
        pub rule sexpr_app() -> SExpr = spanned(<expr_app()>)

        #[cache]
        pub rule expr_atom() -> Expr
            = tok(ParenL) e:expr() tok(ParenR) { e }
            / tok(ParenL) e1:sexpr() tok(Comma) m:smult_opt() e2:sexpr() tok(ParenR)
              { Expr::Pair(m, Box::new(e1), Box::new(e2)) }
            / tok(Unit) { Expr::Unit }
            / x:sid() { Expr::Var(x.to_owned()) }
        pub rule sexpr_atom() -> SExpr = spanned(<expr_atom()>)

        // Regular Expressions

        pub rule regex() -> RegexS<u8>
            = quiet!{[Tok(Regex(""))] { crate::regex::Regex::Eps }}
            / quiet!{[Tok(Regex(s))] {? regex_parser::expr_u8(s).map_err(|e| "Failed parsing regex") }}
            / expected!("regex")
        pub rule sregex() -> SRegex = spanned(<regex()>)

        // Regular Expression Words

        pub rule word() -> Word = quiet!{[Tok(Str(s))] { s.to_string() }} / expected!("string")
        pub rule sword() -> SWord = spanned(<word()>)

        // Declarations

        pub rule pattern() -> Pattern
            = tok(ParenL) p1:spattern() tok(Comma) p2:spattern() tok(ParenR) { Pattern::Pair(Box::new(p1), Box::new(p2)) }
            / x:sid() { Pattern::Var(x.to_owned()) }
        pub rule spattern() -> SPattern = spanned(<pattern()>)

        pub rule clause() -> Clause
            = [Braced::Item]? y:sid() ps:spattern()* tok(Equals) e:sexpr() { Clause { id: y, pats: ps, body: e } }
        pub rule sclause() -> SClause = spanned(<clause()>)

        // Whole Programs

        #[cache]
        pub rule program() -> Expr
            = [Braced::Begin] [Braced::Item]? e:expr() [Braced::End] { e }
        pub rule sprogram() -> SExpr = spanned(<program()>)
    }
}

// #[test]
// fn parse_int() {
//     assert_eq!(nix_parser::expr("-323"), Ok(Expr::Int(-323)));
//     assert_eq!(
//         nix_parser::expr_s("-323"),
//         Ok(Spanned::new(Expr::Int(-323), Span { start: 0, end: 4 }))
//     );
// }
