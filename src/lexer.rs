use std::{error::Error, fmt::Display};

use logos::{Lexer, Logos};

use crate::util::{
    peg_logos::SpannedToks,
    span::{Span, Spanned},
};

#[derive(Debug, PartialEq, Clone, Default)]
pub enum LexingError {
    Int,
    Float,
    #[default]
    Other,
}

pub type LexerError = Spanned<LexingError>;

// TODO
impl Display for LexingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{:?}", self)
    }
}

impl Error for LexingError {}

#[derive(Logos, Debug, Clone, Copy, PartialEq)]
#[logos(skip r"[ \t\f]+")] // Ignore this regex pattern between tokens
#[logos(skip r"#[^\n]+")] // Ignore this regex pattern between tokens
#[logos(error = LexingError)]
pub enum Token<'a> {
    // Keywords
    #[token("true")]
    True,
    #[token("false")]
    False,
    #[token("let")]
    Let,
    #[token("in")]
    In,
    #[token("if")]
    If,
    #[token("then")]
    Then,
    #[token("else")]
    Else,
    #[token("or")]
    Or,
    #[token("and")]
    And,
    #[token("import")]
    Import,
    #[token("not")]
    Not,
    #[token("new")]
    New,
    #[token("split")]
    Split,
    #[token("unit")]
    Unit,
    #[token("Unit")]
    UnitT,
    #[token("Int")]
    IntT,
    #[token("Bool")]
    BoolT,
    #[token("String")]
    StringT,
    #[token("drop")]
    Drop,
    #[token("unr")]
    Unr,
    #[token("lin")]
    Lin,
    #[token("left")]
    Left,
    #[token("right")]
    Right,
    #[token("pure")]
    Pure,
    #[token("eff")]
    Eff,
    #[token("send")]
    Send,
    #[token("recv")]
    Recv,
    #[token("return")]
    Return,
    #[token("wait")]
    Wait,
    #[token("term")]
    Term,
    #[token("Chan")]
    Chan,
    #[token("|>")]
    TriRight,
    #[token("case")]
    Case,
    #[token("inj")]
    Inj,
    #[regex("fork|spawn")]
    Fork,

    // Operators
    #[token(";")]
    Semicolon,
    #[token("{")]
    BraceL,
    #[token("}")]
    BraceR,
    #[token("(")]
    ParenL,
    #[token(")")]
    ParenR,
    #[token("[")]
    BracketL,
    #[token("]")]
    BracketR,
    #[token("+")]
    Plus,
    #[regex("->|→")]
    Arrow,
    #[regex("=>|⇒")]
    DoubleArrow,
    #[regex("-|–")]
    Minus,
    #[token("*")]
    Star,
    #[token("⊙")]
    StarOrdL,
    #[token("⊗")]
    StarLin,
    #[token("//")]
    DoubleSlash,
    #[token("/")]
    Slash,
    #[token("<=")]
    Le,
    #[token(">=")]
    Ge,
    #[token("<")]
    Lt,
    #[token(">")]
    Gt,
    #[token("==")]
    DoubleEquals,
    #[token("!=")]
    BangEquals,
    #[token("!")]
    Bang,
    #[token("?")]
    QuestionMark,
    #[token("=")]
    Equals,
    #[token(",")]
    Comma,
    #[token("@")]
    At,
    #[token(":")]
    Colon,
    #[token(".")]
    Period,
    #[regex(r"\\|λ")]
    Lambda,
    #[token("||")]
    DoublePipe,
    #[token("|")]
    Pipe,
    #[regex(r"&&")]
    DoubleAmp,
    #[token("&")]
    Amp,
    #[token("\"")]
    DoubleQuotes,
    #[token("str")]
    ToStr,
    #[token("print")]
    Print,

    // Positive Int
    #[regex(r"[0-9]+", |lex| lex.slice().parse().map_err(|_| LexingError::Int))]
    Int(i64),

    // Positive Float
    #[regex(r"([0-9]+\.[0-9]*(e[0-9]*)?)|([0-9]*\.[0-9]+(e[0-9]*)?)", |lex| lex.slice().parse().map_err(|_| LexingError::Float))]
    Float(f64),

    // String
    #[regex(r#""(\\"|[^"])*""#, |lex| &lex.slice()[1..lex.slice().len()-1])]
    #[regex(r#"'(\\'|[^'])*'"#, |lex| &lex.slice()[1..lex.slice().len()-1])]
    #[regex(r"'''(\\'|[^']|'[^']|''[^'])*'''", |lex| &lex.slice()[3..lex.slice().len()-3])]
    Str(&'a str),

    // Identifier
    #[regex("[a-zA-Z_]+[a-zA-Z0-9_]*")]
    Id(&'a str),

    // Newline, later processed by module `lexer_offside`.
    #[regex("\n|\r\n|\n\r")]
    NewLine,
}

pub fn lex_plain(s: &str) -> impl Iterator<Item = (Result<Token, LexingError>, Span)> + '_ {
    let lex: Lexer<Token> = Token::lexer(s);
    lex.spanned()
}

pub fn lex(src: &str) -> Result<SpannedToks<Token>, LexerError> {
    let lex: Lexer<Token> = Token::lexer(src);
    let toks = lex
        .spanned()
        .map(|(tok, span)| match tok {
            Ok(tok) => Ok(Spanned::new(tok, span)),
            Err(e) => Err(Spanned::new(e, span)),
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(SpannedToks { src, toks })
}

impl<'a> Token<'a> {
    pub fn to_str(&self) -> &'static str {
        match self {
            Token::True => "true",
            Token::False => "false",
            Token::Let => "let",
            Token::In => "in",
            Token::If => "if",
            Token::Then => "then",
            Token::Else => "else",
            Token::Or => "or",
            Token::And => "and",
            Token::Import => "import",
            Token::Not => "not",
            Token::New => "new",
            Token::Split => "split",
            Token::Unit => "unit",
            Token::UnitT => "Unit",
            Token::Drop => "drop",
            Token::Unr => "unr",
            Token::Lin => "lin",
            Token::Left => "left",
            Token::Right => "right",
            Token::Pure => "pure",
            Token::Eff => "eff",
            Token::Semicolon => ";",
            Token::BraceL => "{{",
            Token::BraceR => "}}",
            Token::ParenL => "(",
            Token::ParenR => ")",
            Token::BracketL => "[",
            Token::BracketR => "]",
            Token::Plus => "+",
            Token::Arrow => "→",
            Token::Minus => "-",
            Token::Star => "*",
            Token::DoubleSlash => "//",
            Token::Slash => "/",
            Token::Le => "<",
            Token::Ge => ">",
            Token::Lt => "<=",
            Token::Gt => ">=",
            Token::DoubleEquals => "==",
            Token::BangEquals => "!=",
            Token::Bang => "!",
            Token::Equals => "=",
            Token::Comma => ",",
            Token::At => "@",
            Token::Colon => ":",
            Token::Period => ".",
            Token::Lambda => "λ",
            Token::Pipe => "|",
            Token::Amp => "&",
            Token::Int(_x) => "int",
            Token::Float(_x) => "float",
            Token::Str(_x) => "string",
            Token::Id(_x) => "variable",
            Token::NewLine => "\\n",
            Token::StarOrdL => "⊗",
            Token::StarLin => "⊙",
            Token::Send => "send",
            Token::Recv => "recv",
            Token::Return => "return",
            Token::Wait => "wait",
            Token::Term => "term",
            Token::Chan => "Chan",
            Token::TriRight => "|>",
            Token::Case => "case",
            Token::Inj => "inj",
            Token::Fork => "fork",
            Token::DoubleArrow => "=>",
            Token::QuestionMark => "?",
            Token::DoubleQuotes => "\"",
            Token::DoublePipe => "||",
            Token::DoubleAmp => "&&",
            Token::ToStr => "str",
            Token::Print => "print",
            Token::IntT => "Int",
            Token::BoolT => "Bool",
            Token::StringT => "String",
        }
    }
}
