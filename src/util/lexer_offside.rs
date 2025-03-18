use crate::util::{
    peg_logos::SpannedToks,
    span::{Span, Spanned},
};

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Braced<T> {
    Token(T),
    Begin,
    End,
    Item,
}

pub fn process_indent<T>(
    stoks: SpannedToks<T>,
    mut is_block_start: impl FnMut(&T) -> bool,
    mut is_newline: impl FnMut(&T) -> bool,
) -> SpannedToks<Braced<T>> {
    let mut toks = vec![];
    let mut indent_stack = vec![0];
    let mut waiting = false;
    let mut last_newline = 0;

    toks.push(Spanned::new(Braced::Begin, Span { start: 0, end: 0 }));
    for stok in stoks.toks {
        let tok = stok.val;
        let span = stok.span;
        let span_end = Span {
            start: span.end,
            end: span.end,
        };
        let span_col = span.start - last_newline;

        // Skip newlines but remember their positions.
        if is_newline(&tok) {
            last_newline = span.end;
            continue;
        }

        // Pop indents larger than the start of this token and add corresponding end-tokens.
        let mut drop = 0;
        for i in indent_stack.iter().cloned().rev() {
            if i <= span_col {
                break;
            }
            drop += 1
        }
        for _ in 0..drop {
            indent_stack.pop();
            toks.push(Spanned::new(Braced::End, span_end.clone()));
        }

        // If the current token starts a new item, push a separation token.
        let started_new_item = span_col == *indent_stack.last().unwrap();
        if started_new_item {
            toks.push(Spanned::new(Braced::Item, span_end.clone()));
        }

        // If the previous token started a block, push a new indent from the current token.
        if waiting {
            if drop > 0 || started_new_item {
                // Terminate an empty block.
                toks.push(Spanned::new(Braced::End, span_end.clone()));
            } else {
                toks.push(Spanned::new(Braced::Item, span_end.clone()));
                indent_stack.push(span_col);
            }
            waiting = false;
        }

        let is_start = is_block_start(&tok);

        // Push the current token into the output token stream.
        toks.push(Spanned::new(Braced::Token(tok), span.clone()));

        // If the current token is a start token, start a new block.
        if is_start {
            toks.push(Spanned::new(Braced::Begin, span_end));
            waiting = true;
        }
    }

    // Close all blocks which are still open at the end of the token stream.
    let span_end = Span {
        start: stoks.src.len(),
        end: stoks.src.len(),
    };
    for _ in indent_stack {
        toks.push(Spanned::new(Braced::End, span_end.clone()));
    }

    SpannedToks {
        src: stoks.src,
        toks,
    }
}
