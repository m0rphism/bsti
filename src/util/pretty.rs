#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct PrettyOpts {
    pub indent_by: usize,
    pub max_line_len: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Assoc {
    Left,
    Right,
    None,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct PrettyState {
    pub indent_stack: Vec<usize>,
    pub lines: Vec<String>,
    pub cur_line: String,
    pub prec_level: usize,
    pub assoc: Assoc,
}

pub struct PrettyEnv<'a, 'b, S> {
    pub opts: &'a PrettyOpts,
    pub state: PrettyState,
    pub user_state: &'b mut S,
}

impl PrettyState {
    pub fn new() -> Self {
        Self {
            indent_stack: vec![0],
            lines: vec![],
            cur_line: String::new(),
            prec_level: 0,
            assoc: Assoc::None,
        }
    }
}

impl<'a, 'b, S> PrettyEnv<'a, 'b, S> {
    pub fn new(opts: &'a PrettyOpts, user_state: &'b mut S) -> Self {
        Self {
            opts,
            user_state,
            state: PrettyState::new(),
        }
    }
    pub fn str(&mut self, s: impl AsRef<str>) {
        let mut lines = s.as_ref().split("\n");
        self.state.cur_line += lines.next().unwrap();
        for l in lines {
            self.nl();
            self.state.cur_line += &l;
        }
    }
    pub fn infix(&mut self, prec_level: usize, assoc: Assoc, f: impl FnOnce(&mut Self)) {
        let parens_needed = prec_level < self.state.prec_level
            || prec_level == self.state.prec_level
                && assoc != self.state.assoc
                && self.state.assoc != Assoc::None;
        let old_assoc = self.state.assoc;
        let old_prec_level = self.state.prec_level;
        self.state.assoc = assoc;
        self.state.prec_level = prec_level;
        if parens_needed {
            self.pp("(");
            f(self);
            self.pp(")");
        } else {
            f(self)
        }
        self.state.assoc = old_assoc;
        self.state.prec_level = old_prec_level;
    }
    pub fn pp_prec<P: Pretty<S> + ?Sized>(&mut self, prec_level: usize, x: &P) {
        let tmp = self.state.prec_level;
        self.state.prec_level = prec_level;
        x.pp(self);
        self.state.prec_level = tmp;
    }
    pub fn pp_arg<P: Pretty<S> + ?Sized>(&mut self, assoc: Assoc, x: &P) {
        let tmp = self.state.assoc;
        self.state.assoc = assoc;
        x.pp(self);
        self.state.assoc = tmp;
    }
    pub fn pp_left<P: Pretty<S> + ?Sized>(&mut self, x: &P) {
        self.pp_arg(Assoc::Left, x)
    }
    pub fn pp_right<P: Pretty<S> + ?Sized>(&mut self, x: &P) {
        self.pp_arg(Assoc::Right, x)
    }
    pub fn pp<P: Pretty<S> + ?Sized>(&mut self, x: &P) {
        x.pp(self);
    }
    pub fn nl(&mut self) {
        let mut s = String::new();
        std::mem::swap(&mut s, &mut self.state.cur_line);
        self.state.lines.push(s);
        for _ in 0..*self.state.indent_stack.last().unwrap() {
            self.state.cur_line += " ";
        }
    }
    pub fn block(&mut self, k: impl FnOnce(&mut Self)) {
        let i = *self.state.indent_stack.last().unwrap();
        self.state.indent_stack.push(i + self.opts.indent_by);
        self.nl();
        k(self);
        self.state.indent_stack.pop();
    }
    pub fn block_inline(&mut self, k: impl FnOnce(&mut Self)) {
        self.state
            .indent_stack
            .push(self.state.cur_line.chars().count());
        k(self);
        self.state.indent_stack.pop();
    }
    pub fn pp_sep(&mut self, sep: impl Pretty<S>, ss: impl IntoIterator<Item = impl Pretty<S>>) {
        for (i, s) in ss.into_iter().enumerate() {
            if i != 0 {
                self.pp(&sep)
            }
            self.pp(&s)
        }
    }
}

pub trait Pretty<S> {
    fn pp(&self, p: &mut PrettyEnv<S>);
}

pub fn pretty<S: Default>(opts: &PrettyOpts, p: impl Pretty<S>) -> String {
    pretty_st(opts, &mut S::default(), p)
}

pub fn pretty_def<S: Default>(p: impl Pretty<S>) -> String {
    let p_opts = PrettyOpts {
        indent_by: 2,
        max_line_len: 80,
    };
    pretty(&p_opts, p)
}

pub fn pretty_st<S>(opts: &PrettyOpts, state: &mut S, p: impl Pretty<S>) -> String {
    pretty_env(&mut PrettyEnv::new(opts, state), p)
}

pub fn pretty_st_<S>(
    opts: &PrettyOpts,
    state: &PrettyState,
    user_state: &mut S,
    p: impl Pretty<S>,
) -> String {
    pretty_env(
        &mut PrettyEnv {
            opts,
            state: state.clone(),
            user_state,
        },
        p,
    )
}

pub fn pretty_env<S>(env: &mut PrettyEnv<S>, p: impl Pretty<S>) -> String {
    env.pp(&p);
    let mut s = String::new();
    for l in &env.state.lines {
        s += l;
        s += "\n";
    }
    s += &env.state.cur_line;
    s
}

impl<'a, S, P: Pretty<S> + ?Sized> Pretty<S> for &'a P {
    fn pp(&self, p: &mut PrettyEnv<S>) {
        (**self).pp(p)
    }
}

impl<S, P: Pretty<S> + ?Sized> Pretty<S> for Box<P> {
    fn pp(&self, p: &mut PrettyEnv<S>) {
        p.pp(self.as_ref())
    }
}

impl<S> Pretty<S> for str {
    fn pp(&self, p: &mut PrettyEnv<S>) {
        p.str(self)
    }
}

impl<S> Pretty<S> for String {
    fn pp(&self, p: &mut PrettyEnv<S>) {
        p.str(self)
    }
}

impl<S, P: Pretty<S>> Pretty<S> for Vec<P> {
    fn pp(&self, p: &mut PrettyEnv<S>) {
        for x in self {
            x.pp(p);
        }
    }
}

pub struct SepBy<Sep, Ps> {
    pub sep: Sep,
    pub ps: Ps,
}

impl<'a, Sep, Ps> SepBy<Sep, &'a Ps> {
    pub fn new(sep: Sep, ps: &'a Ps) -> Self {
        Self { sep, ps }
    }
}

impl<'a, S, Sep: Pretty<S>, P: Pretty<S> + 'a, Ps> Pretty<S> for SepBy<Sep, &'a Ps>
where
    &'a Ps: IntoIterator<Item = &'a P>,
{
    fn pp(&self, p: &mut PrettyEnv<S>) {
        p.pp_sep(&self.sep, self.ps.into_iter());
    }
}
