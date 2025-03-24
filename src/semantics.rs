use std::{
    collections::HashMap,
    sync::{
        mpsc::{channel, Receiver, Sender},
        Arc, Mutex,
    },
};

use crate::{
    fresh_var::fresh_var,
    syntax::{Const, Expr, Id, Label, Op1, Op2, Pattern, SExpr, SId, SPattern, SessionOp},
    util::{
        pretty::{pretty_def, Assoc, Pretty},
        span::fake_span,
    },
};

#[derive(Debug, Clone)]
pub enum EvalError {
    UndefinedVar(SId),
    ValMismatch(SExpr, String, Value),
}

#[derive(Debug)]
pub struct RawCell {
    pub sender: Sender<Value>,
    pub receiver: Receiver<Value>,
}
pub type Cell = Arc<Mutex<RawCell>>;

impl RawCell {
    pub fn new() -> (Cell, Sender<Value>, Receiver<Value>) {
        let (s1, r1) = channel();
        let (s2, r2) = channel();
        let cell = Arc::new(Mutex::new(RawCell {
            sender: s2,
            receiver: r1,
        }));
        (cell, s1, r2)
    }
}

#[derive(Debug)]
pub struct RawChan {
    pub receiver: Receiver<Cell>,
    pub sender: Option<Sender<Cell>>,
}

#[derive(Debug, Clone)]
pub struct Chan(Arc<Mutex<RawChan>>);

impl Chan {
    pub fn borrow(&self) -> Chan {
        let mut c = self.0.lock().unwrap();
        let (s, mut r) = channel();
        std::mem::swap(&mut r, &mut c.receiver);
        let c2 = Arc::new(Mutex::new(RawChan {
            receiver: r,
            sender: Some(s),
        }));
        Chan(c2)
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    Abs(Env, SId, SExpr),
    AbsRec(SId, Env, SId, SExpr),
    Const(Const),
    Pair(Box<Value>, Box<Value>),
    Inj(Label, Box<Value>),
    Chan(Chan),
}

impl Pretty<()> for Chan {
    fn pp(&self, p: &mut crate::util::pretty::PrettyEnv<()>) {
        p.pp("Channel")
    }
}

impl Pretty<()> for Value {
    fn pp(&self, p: &mut crate::util::pretty::PrettyEnv<()>) {
        use Assoc::Left as L;
        //use Assoc::None as N;
        use Assoc::Right as R;
        match self {
            Value::Abs(env, x, e) => p.infix(1, R, |p| {
                p.pp("λ[");
                p.pp(env);
                p.pp("] ");
                p.pp(x);
                p.pp(". ");
                p.pp_arg(R, e);
                p.pp("");
            }),
            Value::AbsRec(f, env, x, e) => p.infix(1, R, |p| {
                p.pp(&format!("λ[rec {}][", f.val));
                p.pp(env);
                p.pp("] ");
                p.pp(x);
                p.pp(". ");
                p.pp_arg(R, e);
                p.pp("");
            }),
            Value::Pair(v1, v2) => {
                p.pp("(");
                p.pp(v1);
                p.pp(", ");
                p.pp(v2);
                p.pp(")");
            }
            Value::Const(c) => p.pp(c),
            Value::Inj(l, e) => p.infix(10, L, |p| {
                p.pp("inj ");
                p.pp(l);
                p.pp(" ");
                p.pp_arg(R, e);
            }),
            Value::Chan(c) => p.pp(c),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Env {
    pub env: HashMap<Id, Value>,
}

impl Env {
    pub fn new() -> Self {
        Self {
            env: HashMap::new(),
        }
    }
    pub fn ext(&self, x: Id, v: Value) -> Env {
        let mut env = self.clone();
        env.env.insert(x, v);
        env
    }
    pub fn get(&self, x: &SId) -> Result<Value, EvalError> {
        self.env
            .get(&x.val)
            .cloned()
            .ok_or_else(|| EvalError::UndefinedVar(x.clone()))
    }
}

impl Pretty<()> for Env {
    fn pp(&self, p: &mut crate::util::pretty::PrettyEnv<()>) {
        let mut env = self.env.iter().collect::<Vec<_>>();
        env.sort_by_key(|(x, _v)| *x);
        for (i, (x, v)) in env.into_iter().enumerate() {
            if i != 0 {
                p.pp(", ");
            }
            p.pp(x);
            p.pp(" ↦ ");
            p.pp(v);
        }
    }
}

pub fn linked_cells() -> (Cell, Cell) {
    let (sender1, receiver2) = channel();
    let (sender2, receiver1) = channel();
    let cell1 = Arc::new(Mutex::new(RawCell {
        sender: sender1,
        receiver: receiver1,
    }));
    let cell2 = Arc::new(Mutex::new(RawCell {
        sender: sender2,
        receiver: receiver2,
    }));
    (cell1, cell2)
}

pub fn eval_(env: &Env, e: &SExpr) -> Result<Value, EvalError> {
    match &e.val {
        Expr::Var(x) => env.get(x),
        Expr::Abs(x, e1) => Ok(Value::Abs(env.clone(), x.clone(), *e1.clone())),
        Expr::App(e1, e2) => {
            let v1 = eval_(env, e1)?;
            let v2 = eval_(env, e2)?;
            match v1.clone() {
                Value::Abs(env, x, e) => {
                    let env = env.ext(x.val, v2);
                    eval_(&env, &e)
                }
                Value::AbsRec(f, env, x, e) => {
                    let env = env.ext(f.val, v1.clone()).ext(x.val, v2);
                    eval_(&env, &e)
                }
                _ => Err(EvalError::ValMismatch(
                    e.clone(),
                    format!("function"),
                    v1.clone(),
                )),
            }
        }
        Expr::AppL(e1, e2) => {
            let v1 = eval_(env, e1)?;
            let v2 = eval_(env, e2)?;
            match v2 {
                Value::Abs(env, x, e) => {
                    let env = env.ext(x.val, v1);
                    eval_(&env, &e)
                }
                _ => Err(EvalError::ValMismatch(
                    e.clone(),
                    format!("function"),
                    v1.clone(),
                )),
            }
        }
        Expr::Borrow(x) => {
            let v = env.get(x)?;
            let Value::Chan(c) = v else {
                return Err(EvalError::ValMismatch(
                    e.clone(),
                    format!("channel"),
                    v.clone(),
                ));
            };
            let c2 = c.borrow();
            Ok(Value::Chan(c2))
        }
        Expr::Let(x, e1, e2) => {
            let v1 = eval_(env, e1)?;
            eval_(&env.ext(x.val.clone(), v1), e2)
        }
        Expr::Pair(e1, e2) => {
            let v1 = eval_(env, e1)?;
            let v2 = eval_(env, e2)?;
            Ok(Value::Pair(Box::new(v1), Box::new(v2)))
        }
        Expr::LetPair(x, y, e1, e2) => {
            let v1 = eval_(env, e1)?;
            let Value::Pair(v11, v12) = v1 else {
                return Err(EvalError::ValMismatch(
                    e.clone(),
                    format!("pair"),
                    v1.clone(),
                ));
            };
            eval_(&env.ext(x.val.clone(), *v11).ext(y.val.clone(), *v12), e2)
        }
        Expr::Inj(l, e1) => {
            let v1 = eval_(env, e1)?;
            Ok(Value::Inj(l.val.clone(), Box::new(v1)))
        }
        Expr::CaseSum(e1, cs) => {
            let v1 = eval_(env, e1)?;
            let Value::Inj(l, v1) = &v1 else {
                return Err(EvalError::ValMismatch(
                    e.clone(),
                    format!("variant injection"),
                    v1.clone(),
                ));
            };
            let (_, x, e) = cs.iter().find(|(l2, _x, _e)| *l == **l2).unwrap();
            eval_(&env.ext(x.val.clone(), *v1.clone()), e)
        }
        Expr::Fork(e1) => {
            let env1 = env.clone();
            let e1 = *e1.clone();
            std::thread::spawn(move || {
                // TODO: error propagation
                eval_(&env1, &e1).unwrap();
            });
            Ok(Value::Const(Const::Unit))
        }
        Expr::New(_s) => {
            let (sender1, receiver1) = channel();
            let (sender2, receiver2) = channel();

            let (cell1, cell2) = linked_cells();
            sender1.send(cell1).unwrap();
            sender2.send(cell2).unwrap();

            let c1 = Chan(Arc::new(Mutex::new(RawChan {
                receiver: receiver1,
                sender: None,
            })));
            let c2 = Chan(Arc::new(Mutex::new(RawChan {
                receiver: receiver2,
                sender: None,
            })));

            Ok(Value::Pair(
                Box::new(Value::Chan(c1)),
                Box::new(Value::Chan(c2)),
            ))
        }
        Expr::Send(e1, e2) => {
            let v1 = eval_(env, e1)?;
            let v2 = eval_(env, e2)?;
            let Value::Chan(c) = v2 else {
                return Err(EvalError::ValMismatch(
                    e.clone(),
                    format!("channel"),
                    v2.clone(),
                ));
            };
            let c = c.0.lock().unwrap();
            let cell = c.receiver.recv().unwrap();
            {
                let cell = cell.lock().unwrap();
                cell.sender.send(v1).unwrap();
            }
            if let Some(sender) = &c.sender {
                sender.send(cell).unwrap();
            }
            Ok(Value::Const(Const::Unit))
        }
        Expr::Recv(e1) => {
            let v1 = eval_(env, e1)?;
            let Value::Chan(c) = v1 else {
                return Err(EvalError::ValMismatch(
                    e.clone(),
                    format!("channel"),
                    v1.clone(),
                ));
            };
            let c = c.0.lock().unwrap();
            let cell = c.receiver.recv().unwrap();
            let v2 = {
                let cell = cell.lock().unwrap();
                cell.receiver.recv().unwrap()
            };
            if let Some(sender) = &c.sender {
                sender.send(cell).unwrap();
            }
            Ok(v2)
        }
        Expr::Select(l, e1) => {
            let v1 = eval_(&env, e1)?;
            let Value::Chan(c) = v1 else {
                return Err(EvalError::ValMismatch(
                    e.clone(),
                    format!("channel"),
                    v1.clone(),
                ));
            };
            let c = c.0.lock().unwrap();
            let cell = c.receiver.recv().unwrap();
            {
                let cell = cell.lock().unwrap();
                cell.sender
                    .send(Value::Const(Const::String(l.val.clone())))
                    .unwrap();
            }
            if let Some(sender) = &c.sender {
                sender.send(cell).unwrap();
            }
            Ok(Value::Const(Const::Unit))
        }
        Expr::Offer(e1) => {
            let v1 = eval_(&env, e1)?;
            let Value::Chan(c) = v1 else {
                return Err(EvalError::ValMismatch(
                    e.clone(),
                    format!("channel"),
                    v1.clone(),
                ));
            };
            let co = c.borrow();
            let co = co.0.lock().unwrap();
            let cell = co.receiver.recv().unwrap();
            let v = {
                let cell = cell.lock().unwrap();
                cell.receiver.recv().unwrap()
            };
            let Value::Const(Const::String(l)) = v else {
                return Err(EvalError::ValMismatch(
                    e.clone(),
                    format!("label"),
                    v.clone(),
                ));
            };
            if let Some(sender) = &co.sender {
                sender.send(cell).unwrap();
            }
            Ok(Value::Inj(l, Box::new(Value::Chan(c))))
        }
        Expr::Drop(e1) => {
            let v1 = eval_(env, e1)?;
            let Value::Chan(c) = v1 else {
                return Err(EvalError::ValMismatch(
                    e.clone(),
                    format!("channel"),
                    v1.clone(),
                ));
            };
            let c = c.0.lock().unwrap();
            let cell = c.receiver.recv().unwrap();
            if let Some(sender) = &c.sender {
                sender.send(cell).unwrap();
            }
            Ok(Value::Const(Const::Unit))
        }
        Expr::End(op, e1) => {
            let v1 = eval_(env, e1)?;
            let Value::Chan(c) = v1 else {
                return Err(EvalError::ValMismatch(
                    e.clone(),
                    format!("channel"),
                    v1.clone(),
                ));
            };
            let c = c.0.lock().unwrap();
            let cell = c.receiver.recv().unwrap();
            {
                let cell = cell.lock().unwrap();
                match op {
                    SessionOp::Send => cell.sender.send(Value::Const(Const::Unit)).unwrap(),
                    SessionOp::Recv => {
                        let _ = cell.receiver.recv().unwrap();
                    }
                };
            }
            if let Some(sender) = &c.sender {
                sender.send(cell).unwrap();
            }
            Ok(Value::Const(Const::Unit))
        }
        Expr::Const(c) => Ok(Value::Const(c.clone())),
        Expr::Ann(e1, _t) => eval_(env, e1),
        Expr::Seq(e1, e2) => {
            let _ = eval_(env, e1)?;
            eval_(env, e2)
        }
        Expr::Op1(op1, e1) => {
            let v1 = eval_(env, e1)?;
            let c = match (op1, &v1) {
                (Op1::Neg, Value::Const(Const::Int(v))) => Const::Int(-v),
                (Op1::Neg, _) => {
                    return Err(EvalError::ValMismatch(
                        e.clone(),
                        format!("integer"),
                        v1.clone(),
                    ));
                }
                (Op1::Not, Value::Const(Const::Bool(v))) => Const::Bool(!v),
                (Op1::Not, _) => {
                    return Err(EvalError::ValMismatch(
                        e.clone(),
                        format!("boolean"),
                        v1.clone(),
                    ));
                }
                (Op1::ToStr, v) => Const::String(val_to_str(v)),
                (Op1::Print, v) => {
                    println!("  {}", val_to_str(v));
                    Const::Unit
                }
            };
            Ok(Value::Const(c))
        }
        Expr::Op2(op2, e1, e2) => {
            let v1 = eval_(env, e1)?;
            let v2 = eval_(env, e2)?;
            let c = match (op2, &v1, &v2) {
                (Op2::Add, Value::Const(Const::Int(v1)), Value::Const(Const::Int(v2))) => {
                    Const::Int(v1 + v2)
                }
                (Op2::Add, Value::Const(Const::String(v1)), Value::Const(Const::String(v2))) => {
                    Const::String(format!("{v1}{v2}"))
                }
                (Op2::Sub, Value::Const(Const::Int(v1)), Value::Const(Const::Int(v2))) => {
                    Const::Int(v1 - v2)
                }
                (Op2::Mul, Value::Const(Const::Int(v1)), Value::Const(Const::Int(v2))) => {
                    Const::Int(v1 * v2)
                }
                (Op2::Div, Value::Const(Const::Int(v1)), Value::Const(Const::Int(v2))) => {
                    Const::Int(v1 / v2)
                }
                (Op2::Eq, Value::Const(c1), Value::Const(c2)) => Const::Bool(c1 == c2),
                (Op2::Neq, Value::Const(c1), Value::Const(c2)) => Const::Bool(c1 != c2),
                (Op2::Lt, Value::Const(c1), Value::Const(c2)) => Const::Bool(c1 < c2),
                (Op2::Le, Value::Const(c1), Value::Const(c2)) => Const::Bool(c1 <= c2),
                (Op2::Gt, Value::Const(c1), Value::Const(c2)) => Const::Bool(c1 > c2),
                (Op2::Ge, Value::Const(c1), Value::Const(c2)) => Const::Bool(c1 >= c2),
                (Op2::And, Value::Const(Const::Bool(v1)), Value::Const(Const::Bool(v2))) => {
                    Const::Bool(*v1 && *v2)
                }
                (Op2::Or, Value::Const(Const::Bool(v1)), Value::Const(Const::Bool(v2))) => {
                    Const::Bool(*v1 || *v2)
                }
                _ => {
                    return Err(EvalError::ValMismatch(
                        e.clone(),
                        format!("Operands do not fit operator"), // TODO
                        v1.clone(),
                    ));
                }
            };
            Ok(Value::Const(c))
        }
        Expr::If(e1, e2, e3) => {
            let v1 = eval_(env, e1)?;
            let Value::Const(Const::Bool(b)) = &v1 else {
                return Err(EvalError::ValMismatch(
                    e.clone(),
                    format!("bool"), // TODO
                    v1.clone(),
                ));
            };
            eval_(env, if *b { e2 } else { e3 })
        }
        Expr::LetDecl(x, _t, cs, e2) => {
            let c = cs.first().unwrap();
            let v1 = if c.pats.len() > 0 {
                let mut fun = c.body.clone();
                for p in c.pats.iter().rev() {
                    let y = fresh_var();
                    fun = fake_span(Expr::Abs(
                        y.clone(),
                        Box::new(pattern_to_let_chain(y, p, fun)),
                    ));
                }
                let Expr::Abs(y, e) = fun.val else {
                    unreachable!()
                };
                Value::AbsRec(x.clone(), env.clone(), y, *e)
            } else {
                eval_(env, &c.body)?
            };
            let env = env.ext(x.val.clone(), v1);
            eval_(&env, &e2)
        }
    }
}

pub fn val_to_str(v: &Value) -> String {
    match v {
        Value::Const(Const::String(s)) => s.clone(),
        _ => pretty_def(v),
    }
}

pub fn eval(e: &SExpr) -> Result<Value, EvalError> {
    let env = Env::new();
    let v = eval_(&env, e)?;
    Ok(v)
}

pub fn pattern_to_let_chain(x: SId, p: &SPattern, body: SExpr) -> SExpr {
    match &p.val {
        Pattern::Var(y) => fake_span(Expr::Let(
            y.clone(),
            Box::new(fake_span(Expr::Var(x.clone()))),
            Box::new(body),
        )),
        Pattern::Pair(p1, p2) => {
            let x1 = fresh_var();
            let x2 = fresh_var();
            let body = pattern_to_let_chain(x2.clone(), p2, body);
            let body = pattern_to_let_chain(x1.clone(), p1, body);
            let body = fake_span(Expr::LetPair(
                x1,
                x2,
                Box::new(fake_span(Expr::Var(x.clone()))),
                Box::new(body),
            ));
            body
        }
    }
}
