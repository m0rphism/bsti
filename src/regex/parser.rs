use peg::{error::ParseError, str::LineCol};

use super::regex::Regex;

fn special_char(c: char) -> bool {
    match c {
        '(' | ')' | '[' | ']' | '{' | '}' | '\\' => true,
        '|' | '&' | '*' | '~' | '¬' | 'ε' | '∅' => true,
        _ => false,
    }
}

#[cfg_attr(rustfmt, rustfmt_skip)]
peg::parser! {
    pub grammar regex_parser<'a>() for str {
        pub rule expr_u8() -> Regex<u8>
            = e:expr() { e.to_u8().simplify() }

        pub rule expr() -> Regex<char>
            = e:expr_or() { e }

        pub rule expr_or() -> Regex<char>
            = e1:expr_and() ['|'] e2:expr_or() { Regex::Or(Box::new(e1), Box::new(e2)) }
            / e:expr_and() { e }

        pub rule expr_and() -> Regex<char>
            = e1:expr_seq() ['&'] e2:expr_and() { Regex::And(Box::new(e1), Box::new(e2)) }
            / e:expr_seq() { e }

        pub rule expr_seq() -> Regex<char>
            = e1:expr_un() e2:expr_seq() { Regex::Seq(Box::new(e1), Box::new(e2)) }
            / e:expr_un() { e }

        #[cache_left_rec]
        pub rule expr_un() -> Regex<char>
            = e:expr_un() ['*'] { Regex::Star(Box::new(e)) }
            / ['~'|'¬'] e:expr_un() { Regex::Neg(Box::new(e)) }
            / e:expr_atom() { e }

        pub rule expr_atom() -> Regex<char>
            = ['('] e:expr() [')'] { e }
            / ['∅'] { Regex::Empty }
            / ['ε'] { Regex::Eps }
            / c:letter() { Regex::Char(c) }

        pub rule letter() -> char 
            = c:[c if !special_char(c)] { c }
            / ['\\'] [c if special_char(c)] { c }
    }
}

impl Regex<u8> {
    pub fn from_str(s: &str) -> Result<Self, ParseError<LineCol>> {
        regex_parser::expr(s).map(|e| e.to_u8())
    }
}
impl Regex<char> {
    pub fn from_str(s: &str) -> Result<Self, ParseError<LineCol>> {
        regex_parser::expr(s)
    }
}
