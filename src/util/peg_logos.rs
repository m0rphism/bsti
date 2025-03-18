use std::fmt::Debug;

use peg::{Parse, ParseElem, ParseSlice, RuleResult};

use crate::util::span::Spanned;

pub struct SpannedToks<'a, T: 'a> {
    pub src: &'a str,
    pub toks: Vec<Spanned<T>>,
}

impl<'a, T: 'a> SpannedToks<'a, T> {
    pub fn print_toks_debug(&self)
    where
        T: Debug,
    {
        for t in &self.toks {
            println!("{:?}\t  {:?}", t.span, t.val);
        }
    }
}

impl<'a, T> Parse for SpannedToks<'a, T> {
    type PositionRepr = usize;

    fn start<'input>(&'input self) -> usize {
        0
    }

    fn is_eof<'input>(&'input self, pos: usize) -> bool {
        pos >= self.toks.len()
    }

    fn position_repr<'input>(&'input self, pos: usize) -> Self::PositionRepr {
        if pos < self.toks.len() {
            self.toks[pos].span.start
        } else {
            self.toks.last().unwrap().span.end
        }
    }
}

impl<'input, T: 'input + Copy> ParseElem<'input> for SpannedToks<'input, T> {
    type Element = T;

    fn parse_elem(&'input self, pos: usize) -> RuleResult<T> {
        match self.toks[pos..].first() {
            Some(c) => RuleResult::Matched(pos + 1, **c),
            None => RuleResult::Failed,
        }
    }
}

impl<'input, T: 'input> ParseSlice<'input> for SpannedToks<'input, T> {
    type Slice = &'input str;
    fn parse_slice(&'input self, p1: usize, p2: usize) -> &'input str {
        let p1 = self.position_repr(p1);
        let p2 = self.position_repr(p2);
        &self.src[p1..p2]
    }
}

// pub struct LogosLexer<'a, T: Logos<'a>>(pub Peekable<SpannedIter<'a, T>>);

// impl<'a, T: Logos<'a>> Deref for LogosLexer<'a, T> {
//     type Target = Peekable<SpannedIter<'a, T>>;

//     fn deref(&self) -> &Self::Target {
//         &self.0
//     }
// }
