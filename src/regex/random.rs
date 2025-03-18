use rand::random;

use crate::regex::parser::regex_parser;

use super::Regex;

pub fn rand_regex(max_len: usize) -> Regex<u8> {
    let is_op = |c| c == b'|' || c == b'*';
    let is_paren = |c| c == b'(' || c == b')';
    let is_lhs = |c| !is_op(c) && c != b'(';
    let is_rhs = |c| !is_op(c) && c != b')';

    let num_chars = 3;
    let len = 1 + random::<usize>() % max_len;
    let mut buf = vec![];
    for _ in 0..len {
        let c = 97 + (random::<u8>() % num_chars);
        buf.push(c);
    }
    if len > 2 {
        let num_parens = random::<usize>() % (len / 3);
        for _ in 0..num_parens {
            let begin = random::<usize>() % (len - 2);
            let end = begin + 2 + (random::<usize>() % (len - (begin + 2)));
            if !is_paren(buf[begin]) && !is_paren(buf[end]) {
                let mut count = 0;
                let mut was_neg = false;
                for i in begin + 1..end {
                    if buf[i] == b'(' {
                        count += 1
                    } else if buf[i] == b')' {
                        count -= 1;
                        if count < 0 {
                            was_neg = true;
                            break;
                        }
                    }
                }
                if count == 0 && !was_neg {
                    buf[begin] = b'(';
                    buf[end] = b')';
                }
            }
        }
        let num_binops = random::<usize>() % (len / 3);
        for _ in 0..num_binops {
            let i = 1 + (random::<usize>() % (len - 2));
            if is_lhs(buf[i - 1]) && is_rhs(buf[i + 1]) && !is_paren(buf[i]) {
                buf[i] = b'|';
            }
        }
    }
    if len > 1 {
        let num_unops = random::<usize>() % (len / 2);
        for _ in 0..num_unops {
            let i = 1 + (random::<usize>() % (len - 2));
            if is_lhs(buf[i - 1]) && !is_paren(buf[i]) {
                buf[i] = b'*';
            }
        }
    }
    let s = String::from_utf8(buf).unwrap();
    regex_parser::expr_u8(&s).unwrap()
}
