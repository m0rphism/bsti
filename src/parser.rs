use crate::lexer::Token;
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

        // Constants
        pub rule string() -> Const = quiet!{[Tok(Str(x))] { Const::String(x.to_owned()) }} / expected!("string literal")
        pub rule int() -> Const = quiet!{[Tok(Int(x))] { Const::Int(x) }} / expected!("integer literal")
        pub rule unit() -> Const = tok(Unit) { Const::Unit }
        pub rule bool() -> Const
            = quiet!{tok(True) { Const::Bool(true) }}
            / quiet!{tok(False) { Const::Bool(false) }}
            / expected!("boolean literal")
        pub rule constant() -> Const 
            = quiet!{ string() / int() / bool() / unit() } / expected!("literal")

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

        pub rule session() -> Session
            = tok(Return) { Session::Return }
            / tok(Wait) { Session::End(SessionOp::Recv) }
            / tok(Term) { Session::End(SessionOp::Send) }
            / tok(Bang) t:stype_atom() tok(Period) s:ssession() 
              { Session::Op(SessionOp::Send, Box::new(t), Box::new(s)) }
            / tok(QuestionMark) t:stype_atom() tok(Period) s:ssession() 
              { Session::Op(SessionOp::Recv, Box::new(t), Box::new(s)) }
            / tok(Amp) tok(BraceL) cs:((l:sid() tok(Colon) s:ssession() { (l, s) })** tok(Comma)) tok(Comma)? tok(BraceR)
              { Session::Choice(SessionOp::Recv, cs) }
            / tok(Plus) tok(BraceL) cs:((l:sid() tok(Colon) s:ssession() { (l, s) })** tok(Comma)) tok(Comma)? tok(BraceR)
              { Session::Choice(SessionOp::Send, cs) }
            / tok(Mu) x:sid() tok(Period) s:ssession()
              { Session::Mu(x, Box::new(s)) }
            / x:sid()
              { Session::Var(x) }
            / tok(ParenL) s:session() tok(ParenR) { s }
        pub rule ssession() -> SSession = spanned(<session()>)

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
            / tok(IntT) { Type::Int }
            / tok(BoolT) { Type::Bool }
            / tok(StringT) { Type::String }
            / tok(ParenL) t:type_() tok(ParenR) { t }
            / tok(Chan) s:ssession() { Type::Chan(s) }
            / tok(Lt) cs:((l:sid() tok(Colon) t:stype() { (l , t) }) ** tok(Comma)) tok(Comma)? tok(Gt) { Type::Variant(cs) }
        pub rule stype_atom() -> SType = spanned(<type_atom()>)

        // Expressions

        pub rule expr() -> Expr = e:expr_ann() { e }
        pub rule sexpr() -> SExpr = spanned(<expr()>)

        pub rule expr_ann() -> Expr
            = e:sexpr_lam() tok(Colon) t:stype() { Expr::Ann(Box::new(e), t) }
            / e:expr_lam() { e }
        pub rule sexpr_ann() -> SExpr = spanned(<expr_ann()>)

        #[cache]
        pub rule expr_lam() -> Expr
            = tok(Lambda) x:sid() tok(Period) e:sexpr_lam()
              { Expr::Abs(x, Box::new(e)) }
            / tok(Case) e:sexpr() tok(BraceL)
              cs:((tok(Inj)? l:sid() x:sid() tok(Arrow) tok(BraceL) e:sexpr() tok(BraceR) { (l, x, e) }) ** (tok(Semicolon)?))
              tok(Semicolon)? tok(BraceR)
              { Expr::CaseSum(Box::new(e), cs) }
            / tok(Let) tok(ParenL)? x:sid() tok(Comma) y:sid() tok(ParenR)? tok(Equals) e1:sexpr_ann() tok(In) e2:sexpr_lam()
              { Expr::LetPair(x, y, Box::new(e1), Box::new(e2)) }
            / tok(Let) x:sid() tok(Equals) e1:sexpr_ann() tok(In) e2:sexpr_lam()
              { Expr::Let(x, Box::new(e1), Box::new(e2)) }
            / tok(Let) x:sid() tok(Colon) t:stype() cs:sclause()* tok(In) e:sexpr_lam()
              { Expr::LetDecl(x, t, cs, Box::new(e)) }
            / tok(If) e:sexpr_lam() tok(Then) e1:sexpr_lam() tok(Else) e2:sexpr_lam()
              { Expr::If(Box::new(e), Box::new(e1), Box::new(e2)) }
            / e:expr_seq() { e }
        pub rule sexpr_lam() -> SExpr = spanned(<expr_lam()>)

        #[cache_left_rec]
        pub rule expr_seq() -> Expr
            = e1:sexpr_or() tok(Semicolon) e2:sexpr_seq() { Expr::Seq(Box::new(e1), Box::new(e2)) }
            / e:expr_or() { e }
        pub rule sexpr_seq() -> SExpr = spanned(<expr_seq()>)

        #[cache_left_rec]
        pub rule expr_or() -> Expr
            = e1:sexpr_and() (tok(DoublePipe) / tok(Or)) e2:sexpr_or() { Expr::Op2(Op2::Or, Box::new(e1), Box::new(e2)) }
            / e:expr_and() { e }
        pub rule sexpr_or() -> SExpr = spanned(<expr_or()>)

        #[cache_left_rec]
        pub rule expr_and() -> Expr
            = e1:sexpr_not() (tok(DoubleAmp) / tok(And)) e2:sexpr_and() { Expr::Op2(Op2::And, Box::new(e1), Box::new(e2)) }
            / e:expr_not() { e }
        pub rule sexpr_and() -> SExpr = spanned(<expr_and()>)

        #[cache_left_rec]
        pub rule expr_not() -> Expr
            = (tok(Not) / tok(Bang)) e:sexpr_not() { Expr::Op1(Op1::Not, Box::new(e)) }
            / e:expr_cmp() { e }
        pub rule sexpr_not() -> SExpr = spanned(<expr_not()>)

        #[cache_left_rec]
        pub rule expr_cmp() -> Expr
            = e1:sexpr_add() tok(Lt) e2:sexpr_add() { Expr::Op2(Op2::Lt, Box::new(e1), Box::new(e2)) }
            / e1:sexpr_add() tok(Le) e2:sexpr_add() { Expr::Op2(Op2::Le, Box::new(e1), Box::new(e2)) }
            / e1:sexpr_add() tok(Gt) e2:sexpr_add() { Expr::Op2(Op2::Gt, Box::new(e1), Box::new(e2)) }
            / e1:sexpr_add() tok(Ge) e2:sexpr_add() { Expr::Op2(Op2::Ge, Box::new(e1), Box::new(e2)) }
            / e1:sexpr_add() tok(DoubleEquals) e2:sexpr_add() { Expr::Op2(Op2::Eq, Box::new(e1), Box::new(e2)) }
            / e1:sexpr_add() tok(BangEquals) e2:sexpr_add() { Expr::Op2(Op2::Neq, Box::new(e1), Box::new(e2)) }
            / e:expr_add() { e }
        pub rule sexpr_cmp() -> SExpr = spanned(<expr_cmp()>)

        #[cache_left_rec]
        pub rule expr_add() -> Expr
            = e1:sexpr_sub() tok(Plus) e2:sexpr_add() { Expr::Op2(Op2::Add, Box::new(e1), Box::new(e2)) }
            / e:expr_sub() { e }
        pub rule sexpr_add() -> SExpr = spanned(<expr_add()>)

        #[cache_left_rec]
        pub rule expr_sub() -> Expr
            = e1:sexpr_sub() tok(Minus) e2:sexpr_mul() { Expr::Op2(Op2::Sub, Box::new(e1), Box::new(e2)) }
            / e:expr_mul() { e }
        pub rule sexpr_sub() -> SExpr = spanned(<expr_sub()>)

        #[cache_left_rec]
        pub rule expr_mul() -> Expr
            = e1:sexpr_neg() tok(Star) e2:sexpr_mul() { Expr::Op2(Op2::Mul, Box::new(e1), Box::new(e2)) }
            / e1:sexpr_neg() tok(Slash) e2:sexpr_mul() { Expr::Op2(Op2::Div, Box::new(e1), Box::new(e2)) }
            / e:expr_neg() { e }
        pub rule sexpr_mul() -> SExpr = spanned(<expr_mul()>)

        #[cache_left_rec]
        pub rule expr_neg() -> Expr
            = tok(Minus) e:sexpr_neg() { Expr::Op1(Op1::Neg, Box::new(e)) }
            / e:expr_app() { e }
        pub rule sexpr_neg() -> SExpr = spanned(<expr_neg()>)

        #[cache_left_rec]
        pub rule expr_app() -> Expr
            = tok(New) s:ssession() { Expr::New(s) }
            / tok(Send) e1:sexpr_atom() e2:sexpr_atom() { Expr::Send(Box::new(e1), Box::new(e2)) }
            / tok(Recv) e:sexpr_atom() { Expr::Recv(Box::new(e)) }
            / tok(Drop) e:sexpr_atom() { Expr::Drop(Box::new(e)) }
            / tok(Term) e:sexpr_atom() { Expr::End(SessionOp::Send, Box::new(e)) }
            / tok(Wait) e:sexpr_atom() { Expr::End(SessionOp::Recv, Box::new(e)) }
            / tok(Inj) l:sid() e:sexpr_atom() { Expr::Inj(l, Box::new(e)) }
            / tok(Fork) e:sexpr_atom() { Expr::Fork(Box::new(e)) }
            / tok(ToStr) e:sexpr_atom() { Expr::Op1(Op1::ToStr, Box::new(e)) }
            / tok(Print) e:sexpr_atom() { Expr::Op1(Op1::Print, Box::new(e)) }
            / e1:sexpr_app() tok(TriRight) e2:sexpr_atom() { Expr::AppR(Box::new(e1), Box::new(e2)) }
            / e1:sexpr_app() e2:sexpr_atom() { Expr::App(Box::new(e1), Box::new(e2)) }
            / e:expr_atom() { e }
        pub rule sexpr_app() -> SExpr = spanned(<expr_app()>)

        #[cache]
        pub rule expr_atom() -> Expr
            = tok(ParenL) e:expr() tok(ParenR) { e }
            / tok(ParenL) e1:sexpr() tok(Comma) e2:sexpr() tok(ParenR)
              { Expr::Pair(Box::new(e1), Box::new(e2)) }
            / tok(Amp) x:sid() { Expr::Borrow(x) }
            / c:constant() { Expr::Const(c) }
            / x:sid() { Expr::Var(x.to_owned()) }
        pub rule sexpr_atom() -> SExpr = spanned(<expr_atom()>)

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
