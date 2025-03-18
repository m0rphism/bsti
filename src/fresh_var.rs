use crate::{syntax::SId, util::span::fake_span};

pub fn fresh_var() -> SId {
    static mut NEXT_FRESH_VAR: usize = 0;
    let n = unsafe {
        NEXT_FRESH_VAR += 1;
        NEXT_FRESH_VAR - 1
    };
    fake_span(format!("FRESH:{}", n))
}
