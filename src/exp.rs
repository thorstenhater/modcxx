use crate::usr::{self, Inventory};
use crate::{err::Result, loc::Location, usr::Uses, Map, Set};
pub use rug::Rational;
use std::fmt::{self, Debug};
use std::ops::{Deref, DerefMut};

pub const MAX_PRECISION: u32 = 100;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct WithLocation<T: Clone + PartialEq + Eq + Debug> {
    pub loc: Location,
    pub data: T,
}

impl<T: Clone + PartialEq + Eq + Debug> WithLocation<T> {
    pub fn new(t: T, loc: Location) -> Self {
        WithLocation { loc, data: t }
    }
}

impl<T: Clone + PartialEq + Eq + Debug> Deref for WithLocation<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl<T: Clone + PartialEq + Eq + Debug> DerefMut for WithLocation<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.data
    }
}

impl<T: Clone + PartialEq + Eq + Debug> AsRef<T> for WithLocation<T> {
    fn as_ref(&self) -> &T {
        &self.data
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Operator {
    Nil,
    Not,
    Add,
    Sub,
    Mul,
    Div,
    Neg,
    Pow,
    LT,
    GT,
    GE,
    LE,
    Eq,
    NEq,
    And,
    Or,
    Dt,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Independent {
    pub var: String,
    pub from: String,
    pub to: String,
    pub with: String,
    pub unit: Option<Unit>,
}

impl fmt::Debug for Operator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let op = match self {
            Operator::Eq => "==",
            Operator::NEq => "!=",
            Operator::GE => ">=",
            Operator::GT => ">",
            Operator::LE => "<=",
            Operator::LT => "<",
            Operator::And => "&&",
            Operator::Or => "||",
            Operator::Add => "+",
            Operator::Sub => "-",
            Operator::Mul => "*",
            Operator::Div => "/",
            Operator::Not => "!",
            Operator::Neg => "-",
            Operator::Pow => "^",
            Operator::Dt => "'",
            _ => unreachable!(),
        };
        write!(f, "{}", op)
    }
}

impl fmt::Display for Operator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let op = match self {
            Operator::Eq => "==",
            Operator::NEq => "!=",
            Operator::GE => ">=",
            Operator::GT => ">",
            Operator::LE => "<=",
            Operator::LT => "<",
            Operator::And => "&&",
            Operator::Or => "||",
            Operator::Add => "+",
            Operator::Sub => "-",
            Operator::Mul => "*",
            Operator::Div => "/",
            Operator::Not => "!",
            Operator::Neg => "-",
            Operator::Pow => "^",
            Operator::Dt => "'",
            _ => unreachable!(),
        };
        write!(f, "{}", op)
    }
}

pub type Block = WithLocation<BlockT>;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct BlockT {
    pub locals: Vec<Symbol>,
    pub stmnts: Vec<Statement>,
}

impl Block {
    pub fn block(locals: &[Symbol], stmnts: &[Statement], loc: Location) -> Self {
        Block {
            data: BlockT {
                locals: locals.to_vec(),
                stmnts: stmnts.to_vec(),
            },
            loc,
        }
    }

    pub fn splat_blocks(&self) -> Result<Self> {
        let mut res = self.clone();
        let mut done = false;
        while !done {
            done = true;
            let mut stmnts = Vec::new();
            let mut locals = res.locals.clone();
            for stmnt in &res.stmnts {
                if let StatementT::Block(inner) = &stmnt.data {
                    let mut substs = Map::new();
                    for local in &inner.locals {
                        let mut nm = local.name.to_string();
                        let mut idx = 0;
                        while locals.iter().any(|l| l.name == nm) {
                            nm = format!("{}_{}", local.name, idx);
                            idx += 1;
                        }
                        locals.push(local.rename(&nm));
                        substs.insert(local.name.to_string(), nm);
                    }
                    for stmnt in &inner.stmnts {
                        stmnts.push(stmnt.rename_all(&substs)?);
                    }
                    done = false;
                } else {
                    stmnts.push(stmnt.clone());
                }
            }
            res.data.locals = locals;
            res.data.stmnts = stmnts;
        }
        Ok(res)
    }

    fn substitute(&self, from: &ExpressionT, to: &ExpressionT) -> Result<Self> {
        let mut res = self.clone();
        for stmnt in res.stmnts.iter_mut() {
            *stmnt = stmnt.substitute(from, to)?;
        }
        Ok(res)
    }

    pub fn rename_all(&self, lut: &Map<String, String>) -> Result<Self> {
        let locals = self
            .locals
            .iter()
            .map(|l| l.rename_all(lut))
            .collect::<Result<Vec<_>>>()?;
        let stmnts = self
            .stmnts
            .iter()
            .map(|l| l.rename_all(lut))
            .collect::<Result<Vec<_>>>()?;

        Ok(Self::block(&locals, &stmnts, self.loc))
    }
}

impl Uses for Block {
    fn uses(&self) -> Inventory {
        let mut res = Inventory::new();
        for stmnt in &self.stmnts {
            res.merge(&stmnt.uses());
        }
        for local in &self.locals {
            if let Some(e) = res.0.get_mut(&local.name) {
                e.writes.iter_mut().for_each(|e| e.kind = usr::Kind::Local);
                e.reads.iter_mut().for_each(|e| e.kind = usr::Kind::Local);
            }
        }
        res
    }
}

pub type Statement = WithLocation<StatementT>;

impl Statement {
    pub fn solve_default(lhs: &str, loc: Location) -> Self {
        Self::new(StatementT::Solve(lhs.to_string(), SolveT::Default), loc)
    }

    pub fn solve(lhs: &str, m: &str, loc: Location) -> Self {
        Self::new(
            StatementT::Solve(lhs.to_string(), SolveT::Method(m.to_string())),
            loc,
        )
    }

    pub fn steadystate(lhs: &str, m: &str, loc: Location) -> Self {
        Self::new(
            StatementT::Solve(lhs.to_string(), SolveT::SteadyState(m.to_string())),
            loc,
        )
    }

    pub fn assign(lhs: &str, rhs: Expression, loc: Location) -> Self {
        Self::new(StatementT::Assign(lhs.to_string(), rhs), loc)
    }

    pub fn initial(block: Block, loc: Location) -> Self {
        Self::new(StatementT::Initial(block), loc)
    }

    pub fn conserve(lhs: Expression, rhs: Expression, loc: Location) -> Self {
        Self::new(StatementT::Conserve(lhs, rhs), loc)
    }

    pub fn rate(
        from: Expression,
        to: Expression,
        fwd: Expression,
        bwd: Expression,
        loc: Location,
    ) -> Self {
        Statement::new(StatementT::Rate(from, to, fwd, bwd), loc)
    }

    pub fn linear(lhs: Expression, rhs: Expression, loc: Location) -> Self {
        Statement::new(StatementT::Linear(lhs, rhs), loc)
    }

    pub fn ret(rhs: Expression, loc: Location) -> Self {
        Statement::new(StatementT::Return(rhs), loc)
    }

    pub fn derivative(lhs: &str, rhs: Expression, loc: Location) -> Self {
        Statement::new(StatementT::Derivative(lhs.to_string(), rhs), loc)
    }

    pub fn if_then_else(i: Expression, t: Block, e: Option<Block>, loc: Location) -> Self {
        Statement::new(StatementT::IfThenElse(i, t, e), loc)
    }

    pub fn block(block: Block) -> Self {
        Statement::new(StatementT::Block(block.clone()), block.loc)
    }

    pub fn call(fun: &str, args: Vec<Expression>, loc: Location) -> Self {
        Statement::new(StatementT::Call(fun.to_string(), args), loc)
    }

    pub fn substitute(&self, from: &ExpressionT, to: &ExpressionT) -> Result<Self> {
        let mut res = self.clone();
        match res.data {
            StatementT::Linear(ref mut lhs, ref mut rhs) => {
                *lhs = lhs.substitute(from, to)?;
                *rhs = rhs.substitute(from, to)?;
            }
            StatementT::Assign(ref mut lhs, ref mut rhs) => {
                if let ExpressionT::Variable(x) = &to {
                    if let ExpressionT::Variable(y) = &from {
                        if lhs == y {
                            *lhs = x.to_string();
                        }
                    }
                }
                *rhs = rhs.substitute(from, to)?;
            }
            StatementT::Return(ref mut rhs) => {
                *rhs = rhs.substitute(from, to)?;
            }
            StatementT::Block(ref mut blk) => *blk = blk.substitute(from, to)?,
            StatementT::Call(_, ref mut args) => {
                for ex in args.iter_mut() {
                    *ex = ex.substitute(from, to)?;
                }
            }
            StatementT::Conserve(ref mut lhs, ref mut rhs) => {
                *lhs = lhs.substitute(from, to)?;
                *rhs = rhs.substitute(from, to)?;
            }
            StatementT::Derivative(_, ref mut rhs) => {
                *rhs = rhs.substitute(from, to)?;
            }
            StatementT::IfThenElse(ref mut c, ref mut t, ref mut e) => {
                *c = c.substitute(from, to)?;
                *t = t.substitute(from, to)?;
                if let Some(ref mut i) = e {
                    *i = i.substitute(from, to)?;
                }
            }
            StatementT::Initial(_) => {
                unimplemented!()
            }
            StatementT::Rate(ref mut f, ref mut t, ref mut fwd, ref mut bwd) => {
                *f = f.substitute(from, to)?;
                *t = t.substitute(from, to)?;
                *fwd = fwd.substitute(from, to)?;
                *bwd = bwd.substitute(from, to)?;
            }
            StatementT::Solve(_, _) => {}
        }
        Ok(res)
    }

    pub fn splat_blocks(&self) -> Result<Self> {
        if let StatementT::Block(blk) = &self.data {
            let mut res = self.clone();
            res.data = StatementT::Block(blk.splat_blocks()?);
            Ok(res)
        } else {
            Ok(self.clone())
        }
    }

    pub fn rename_all(&self, lut: &Map<String, String>) -> Result<Self> {
        use StatementT::*;
        let res = match &self.data {
            Assign(lhs, rhs) => {
                let lhs = if let Some(lhs) = lut.get(lhs) {
                    lhs.to_string()
                } else {
                    lhs.to_string()
                };
                let rhs = rhs.rename_all(lut)?;
                Self::assign(&lhs, rhs, self.loc)
            }
            Return(rhs) => Self::ret(rhs.rename_all(lut)?, self.loc),
            Conserve(lhs, rhs) => {
                Self::conserve(lhs.rename_all(lut)?, rhs.rename_all(lut)?, self.loc)
            }
            Rate(a, b, c, d) => Self::rate(
                a.rename_all(lut)?,
                b.rename_all(lut)?,
                c.rename_all(lut)?,
                d.rename_all(lut)?,
                self.loc,
            ),
            Linear(lhs, rhs) => Self::linear(lhs.rename_all(lut)?, rhs.rename_all(lut)?, self.loc),
            Derivative(lhs, rhs) => {
                let lhs = if let Some(lhs) = lut.get(lhs) {
                    lhs.to_string()
                } else {
                    lhs.to_string()
                };
                let rhs = rhs.rename_all(lut)?;
                Self::derivative(&lhs, rhs, self.loc)
            }
            IfThenElse(c, t, None) => {
                Self::if_then_else(c.rename_all(lut)?, t.rename_all(lut)?, None, self.loc)
            }
            IfThenElse(c, t, Some(e)) => Self::if_then_else(
                c.rename_all(lut)?,
                t.rename_all(lut)?,
                Some(e.rename_all(lut)?),
                self.loc,
            ),
            Block(blk) => Self::block(blk.rename_all(lut)?),
            Call(nm, args) => {
                let nm = if let Some(nm) = lut.get(nm) { nm } else { nm };
                let args = args
                    .iter()
                    .map(|a| a.rename_all(lut))
                    .collect::<Result<Vec<_>>>()?;
                Self::call(nm, args, self.loc)
            }
            Initial(blk) => Self::initial(blk.rename_all(lut)?, self.loc),
            _ => unreachable!(),
        };
        Ok(res)
    }

    pub fn substitute_if<F>(&self, pred: &mut F) -> Result<Self>
    where
        F: FnMut(&Statement) -> Option<Statement>,
    {
        if let Some(new) = pred(self) {
            return Ok(new);
        }
        match &self.data {
            StatementT::IfThenElse(c, t, e) => {
                let mut t = t.clone();
                for stmnt in t.stmnts.iter_mut() {
                    *stmnt = stmnt.substitute_if(pred)?;
                }
                let e = if let Some(e) = e {
                    let mut e = e.clone();
                    for stmnt in e.stmnts.iter_mut() {
                        *stmnt = stmnt.substitute_if(pred)?;
                    }
                    Some(e)
                } else {
                    None
                };
                return Ok(Statement::if_then_else(c.clone(), t, e, self.loc));
            }
            StatementT::Block(inner) => {
                let mut inner = inner.clone();
                for stmnt in inner.stmnts.iter_mut() {
                    *stmnt = stmnt.substitute_if(pred)?;
                }
                return Ok(Statement::block(inner));
            }
            _ => return Ok(self.clone()),
        }
    }
}

impl Uses for Statement {
    fn uses(&self) -> Inventory {
        let mut res = Inventory::new();
        let entry = usr::Use {
            args: 0,
            src: self.loc,
            kind: usr::Kind::Global,
        };
        match &self.data {
            StatementT::Linear(lhs, rhs) => {
                for v in rhs.variables().into_iter() {
                    res.0.entry(v).or_default().reads.push(entry);
                }
                for v in lhs.variables().into_iter() {
                    res.0.entry(v).or_default().writes.push(entry);
                }
            }
            StatementT::Assign(lhs, rhs) => {
                for (k, v) in rhs.uses().into_iter() {
                    res.0.entry(k).or_default().merge(&v);
                }
                res.0.entry(lhs.to_string()).or_default().writes.push(entry);
            }
            StatementT::Return(rhs) => {
                for (k, v) in rhs.uses().into_iter() {
                    res.0.entry(k).or_default().merge(&v);
                }
            }
            StatementT::Call(fun, args) => {
                for e in args {
                    for (k, v) in e.uses().into_iter() {
                        res.0.entry(k).or_default().merge(&v);
                    }
                }
                res.0
                    .entry(fun.to_string())
                    .or_default()
                    .calls
                    .push(usr::Use {
                        args: args.len(),
                        src: self.loc,
                        kind: usr::Kind::Global,
                    });
            }
            StatementT::Initial(blk) | StatementT::Block(blk) => {
                for (k, v) in blk.uses().into_iter() {
                    res.0.entry(k).or_default().merge(&v);
                }
            }
            StatementT::Conserve(l, r) => {
                for var in l.variables().into_iter() {
                    let e = res.0.entry(var).or_default();
                    e.reads.push(entry);
                    e.writes.push(entry);
                }
                for var in r.variables().into_iter() {
                    let e = res.0.entry(var).or_default();
                    e.reads.push(entry);
                    e.writes.push(entry);
                }
            }
            StatementT::Rate(l, r, f, b) => {
                for var in l.variables() {
                    let e = res.0.entry(var).or_default();
                    e.reads.push(entry);
                    e.writes.push(entry);
                }
                for var in r.variables().into_iter() {
                    let e = res.0.entry(var).or_default();
                    e.reads.push(entry);
                    e.writes.push(entry);
                }
                for var in f.variables().into_iter() {
                    res.0.entry(var).or_default().reads.push(entry);
                }
                for var in b.variables().into_iter() {
                    res.0.entry(var).or_default().reads.push(entry);
                }
            }
            StatementT::Derivative(nm, ex) => {
                for (k, v) in ex.uses().into_iter() {
                    res.0.entry(k).or_default().merge(&v);
                }
                res.0
                    .entry(format!("{nm}'"))
                    .or_default()
                    .writes
                    .push(entry);
            }
            StatementT::IfThenElse(c, t, e) => {
                for (k, v) in c.uses().into_iter() {
                    res.0.entry(k).or_default().merge(&v);
                }
                for (k, v) in t.uses().into_iter() {
                    res.0.entry(k).or_default().merge(&v);
                }
                if let Some(e) = e {
                    for (k, v) in e.uses().into_iter() {
                        res.0.entry(k).or_default().merge(&v);
                    }
                }
            }
            StatementT::Solve(what, _) => {
                res.0
                    .entry(what.to_string())
                    .or_default()
                    .solves
                    .push(entry);
            }
        }
        res
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum SolveT {
    Default,
    Method(String),
    SteadyState(String),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum StatementT {
    Assign(String, Expression),
    Return(Expression),
    Conserve(Expression, Expression),
    Rate(Expression, Expression, Expression, Expression),
    Linear(Expression, Expression),
    Derivative(String, Expression),
    IfThenElse(Expression, Block, Option<Block>),
    Block(Block),
    Solve(String, SolveT),
    Call(String, Vec<Expression>),
    Initial(Block), // This is _only_ ever for NET_RECEIVE... I hate NMODL
}

pub type Expression = WithLocation<ExpressionT>;

impl Expression {
    pub fn unary(op: Operator, rhs: Expression, loc: Location) -> Self {
        Expression::new(ExpressionT::Unary(op, Box::new(rhs)), loc)
    }

    pub fn binary(lhs: Expression, op: Operator, rhs: Expression, loc: Location) -> Self {
        Expression::new(ExpressionT::Binary(Box::new(lhs), op, Box::new(rhs)), loc)
    }

    pub fn mul(lhs: Expression, rhs: Expression, loc: Location) -> Self {
        Expression::new(
            ExpressionT::Binary(Box::new(lhs), Operator::Mul, Box::new(rhs)),
            loc,
        )
    }

    pub fn div(lhs: Expression, rhs: Expression, loc: Location) -> Self {
        Expression::new(
            ExpressionT::Binary(Box::new(lhs), Operator::Div, Box::new(rhs)),
            loc,
        )
    }

    pub fn neg(rhs: Expression, loc: Location) -> Self {
        Expression::new(ExpressionT::Unary(Operator::Neg, Box::new(rhs)), loc)
    }

    pub fn not(rhs: Expression, loc: Location) -> Self {
        Expression::new(ExpressionT::Unary(Operator::Not, Box::new(rhs)), loc)
    }
    pub fn pow(lhs: Expression, rhs: Expression, loc: Location) -> Self {
        Expression::new(
            ExpressionT::Binary(Box::new(lhs), Operator::Pow, Box::new(rhs)),
            loc,
        )
    }

    pub fn add(lhs: Expression, rhs: Expression, loc: Location) -> Self {
        Expression::new(
            ExpressionT::Binary(Box::new(lhs), Operator::Add, Box::new(rhs)),
            loc,
        )
    }

    pub fn sub(lhs: Expression, rhs: Expression, loc: Location) -> Self {
        Expression::new(
            ExpressionT::Binary(Box::new(lhs), Operator::Sub, Box::new(rhs)),
            loc,
        )
    }

    pub fn float<T>(val: T, loc: Location) -> Self
    where
        Rational: From<T>,
    {
        Expression::new(ExpressionT::Number(Rational::from(val)), loc)
    }

    pub fn number(var: &str, loc: Location) -> Self {
        Expression::new(
            ExpressionT::Number(Rational::from_f64(var.parse::<f64>().unwrap()).unwrap()),
            loc,
        )
    }

    pub fn string(var: &str, loc: Location) -> Self {
        Expression::new(ExpressionT::String(var.to_string()), loc)
    }

    pub fn variable(var: &str, loc: Location) -> Self {
        Expression::new(ExpressionT::Variable(var.to_string()), loc)
    }

    pub fn call(fun: &str, args: Vec<Expression>, loc: Location) -> Self {
        Expression::new(ExpressionT::Call(fun.to_string(), args), loc)
    }

    pub fn variables(&self) -> Set<String> {
        let mut res = Set::new();
        match &self.data {
            ExpressionT::Variable(v) => {
                res.insert(v.to_string());
            }
            ExpressionT::String(_) | ExpressionT::Number(_) => {}
            ExpressionT::Unary(_, e) => {
                res.append(&mut e.variables());
            }
            ExpressionT::Binary(l, _, r) => {
                res.append(&mut l.variables());
                res.append(&mut r.variables());
            }
            ExpressionT::Call(f, es) => {
                res.insert(f.to_string());
                for e in es {
                    res.append(&mut e.variables());
                }
            }
        }
        res
    }

    pub fn substitute(&self, from: &ExpressionT, to: &ExpressionT) -> Result<Self> {
        let mut res = self.clone();
        match res.data {
            ref mut ex if ex == from => {
                *ex = to.clone();
            }
            ExpressionT::Binary(ref mut l, _, ref mut r) => {
                *l = Box::new(l.substitute(from, to)?);
                *r = Box::new(r.substitute(from, to)?);
            }
            ExpressionT::Unary(_, ref mut r) => {
                *r = Box::new(r.substitute(from, to)?);
            }
            ExpressionT::Call(ref mut fun, ref mut args) => {
                if let ExpressionT::Variable(x) = &to {
                    if fun == x {
                        *fun = x.to_string();
                    }
                }
                for arg in args.iter_mut() {
                    *arg = arg.substitute(from, to)?;
                }
            }
            ExpressionT::Variable(_) | ExpressionT::Number(_) | ExpressionT::String(_) => {}
        }
        Ok(res)
    }

    pub fn substitute_if<F>(&self, pred: &mut F) -> Result<Self>
    where
        F: FnMut(&Expression) -> Option<Expression>,
    {
        if let Some(new) = pred(self) {
            Ok(new)
        } else {
            let mut res = self.clone();
            match res.data {
                ExpressionT::Binary(ref mut l, _, ref mut r) => {
                    *l = Box::new(l.substitute_if(pred)?);
                    *r = Box::new(r.substitute_if(pred)?);
                }
                ExpressionT::Unary(_, ref mut r) => {
                    *r = Box::new(r.substitute_if(pred)?);
                }
                ExpressionT::Call(_, ref mut args) => {
                    for arg in args.iter_mut() {
                        *arg = arg.substitute_if(pred)?;
                    }
                }
                ExpressionT::Variable(_) | ExpressionT::Number(_) | ExpressionT::String(_) => {}
            }
            Ok(res)
        }
    }

    pub fn rename_all(&self, lut: &Map<String, String>) -> Result<Self> {
        use ExpressionT::*;
        let res = match &self.data {
            Unary(op, ex) => Self::unary(*op, ex.rename_all(lut)?, self.loc),
            Binary(lhs, op, rhs) => {
                Self::binary(lhs.rename_all(lut)?, *op, rhs.rename_all(lut)?, self.loc)
            }
            Variable(v) => Self::variable(lut.get(v).unwrap_or(v), self.loc),
            Number(_) => self.clone(),
            String(_) => self.clone(),
            Call(fun, args) => {
                let args = args
                    .iter()
                    .map(|a| a.rename_all(lut))
                    .collect::<Result<Vec<_>>>()?;
                let fun = lut.get(fun).unwrap_or(fun);
                Self::call(fun, args, self.loc)
            }
        };
        Ok(res)
    }
}

impl Uses for Expression {
    fn uses(&self) -> Inventory {
        let mut res = Inventory::new();
        match &self.data {
            ExpressionT::Variable(v) => {
                res.0
                    .entry(v.to_string())
                    .or_default()
                    .reads
                    .push(usr::Use {
                        args: 0,
                        src: self.loc,
                        kind: usr::Kind::Global,
                    })
            }
            ExpressionT::String(_) | ExpressionT::Number(_) => {}
            ExpressionT::Unary(_, e) => {
                for (k, v) in e.uses().into_iter() {
                    res.0.entry(k).or_default().merge(&v);
                }
            }
            ExpressionT::Binary(l, _, r) => {
                for (k, v) in l.uses().into_iter() {
                    res.0.entry(k).or_default().merge(&v);
                }
                for (k, v) in r.uses().into_iter() {
                    res.0.entry(k).or_default().merge(&v);
                }
            }
            // Calls evaluate args left -> right _then_ call the functions.
            ExpressionT::Call(f, es) => {
                for e in es {
                    for (k, v) in e.uses().into_iter() {
                        res.0.entry(k).or_default().merge(&v);
                    }
                }
                res.0
                    .entry(f.to_string())
                    .or_default()
                    .calls
                    .push(usr::Use {
                        args: es.len(),
                        src: self.loc,
                        kind: usr::Kind::Global,
                    });
            }
        }
        res
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ExpressionT {
    Unary(Operator, Box<Expression>),
    Binary(Box<Expression>, Operator, Box<Expression>),
    Variable(String),
    Number(Rational),
    String(String),
    Call(String, Vec<Expression>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Access {
    RO,
    RW,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VariableT {
    pub name: String,
    pub unit: Option<Unit>,
    pub range: Option<(String, String)>,
    pub start: Option<String>,
    pub access: Access,
}

pub type Variable = WithLocation<VariableT>;

impl Symbol {
    fn variable(
        name: &str,
        unit: Option<Unit>,
        range: Option<(String, String)>,
        start: Option<String>,
        access: Access,
        loc: Location,
    ) -> Self {
        Variable::new(
            VariableT {
                name: name.to_string(),
                unit,
                range,
                start,
                access,
            },
            loc,
        )
    }

    pub fn parameter(
        name: &str,
        unit: Option<Unit>,
        range: Option<(String, String)>,
        start: Option<String>,
        loc: Location,
    ) -> Self {
        Self::variable(name, unit, range, start, Access::RO, loc)
    }

    pub fn state(
        name: &str,
        unit: Option<Unit>,
        range: Option<(String, String)>,
        start: Option<String>,
        loc: Location,
    ) -> Self {
        Self::variable(name, unit, range, start, Access::RW, loc)
    }

    pub fn argument(name: &str, unit: Option<Unit>, loc: Location) -> Self {
        Self::variable(name, unit, None, None, Access::RO, loc)
    }

    pub fn assigned(
        name: &str,
        unit: Option<Unit>,
        range: Option<(String, String)>,
        start: Option<String>,
        loc: Location,
    ) -> Self {
        Self::variable(name, unit, range, start, Access::RW, loc)
    }

    pub fn global(name: &str, loc: Location) -> Self {
        Self::variable(name, None, None, None, Access::RW, loc)
    }

    pub fn constant(name: &str, val: &str, unit: Option<Unit>, loc: Location) -> Self {
        Self::variable(name, unit, None, Some(val.to_string()), Access::RO, loc)
    }

    pub fn known(name: &str, unit: Option<Unit>, loc: Location) -> Self {
        Self::variable(name, unit, None, None, Access::RO, loc)
    }

    pub fn readonly(name: &str, loc: Location) -> Self {
        Self::variable(name, None, None, None, Access::RO, loc)
    }

    pub fn local(name: &str, loc: Location) -> Self {
        Self::variable(name, None, None, None, Access::RW, loc)
    }

    pub fn rename(&self, nm: &str) -> Self {
        let mut new = self.clone();
        new.name = nm.to_string();
        new
    }

    pub fn rename_all(&self, new: &Map<String, String>) -> Result<Self> {
        let mut res = self.clone();
        if let Some(nm) = new.get(&self.name) {
            res.name = nm.to_string();
        }
        Ok(res)
    }
}

pub type Symbol = WithLocation<VariableT>;

pub type Unit = Expression;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CallableT {
    pub name: String,
    pub args: Option<Vec<Symbol>>,
    pub unit: Option<Unit>,
    pub body: Block,
}

pub type Callable = WithLocation<CallableT>;

impl Callable {
    pub fn procedure(
        name: &str,
        args: &[Symbol],
        unit: Option<Unit>,
        body: Block,
        loc: Location,
    ) -> Self {
        Callable::new(
            CallableT {
                name: name.to_string(),
                args: Some(args.to_vec()),
                unit,
                body,
            },
            loc,
        )
    }

    pub fn headless(name: &str, body: Block, loc: Location) -> Self {
        Callable::new(
            CallableT {
                name: name.to_string(),
                args: None,
                unit: None,
                body,
            },
            loc,
        )
    }

    pub fn initial(body: Block, loc: Location) -> Self {
        Self::headless("INITIAL", body, loc)
    }

    pub fn breakpoint(body: Block, loc: Location) -> Self {
        Self::headless("BREAKPOINT", body, loc)
    }

    pub fn kinetic(name: &str, body: Block, loc: Location) -> Self {
        Self::headless(name, body, loc)
    }

    pub fn linear(name: &str, body: Block, loc: Location) -> Self {
        Self::headless(name, body, loc)
    }

    pub fn derivative(name: &str, body: Block, loc: Location) -> Self {
        Self::headless(name, body, loc)
    }

    pub fn function(
        name: &str,
        args: Vec<Symbol>,
        unit: Option<Unit>,
        body: Block,
        loc: Location,
    ) -> Self {
        Callable::new(
            CallableT {
                name: name.to_string(),
                args: Some(args.to_vec()),
                unit,
                body,
            },
            loc,
        )
    }
}

impl Uses for Callable {
    fn uses(&self) -> Inventory {
        let mut res = self.body.uses();
        if let Some(args) = &self.args {
            for arg in args {
                if let Some(e) = res.0.get_mut(&arg.name) {
                    e.reads
                        .iter_mut()
                        .for_each(|r| r.kind = usr::Kind::Argument);
                    e.writes
                        .iter_mut()
                        .for_each(|r| r.kind = usr::Kind::Argument);
                }
            }
        }
        res
    }
}

#[cfg(test)]
mod test {
    use crate::par::Parser;

    use super::*;

    #[test]
    fn splat() {
        let loc = Location::default();
        let blk = Block::block(
            &[Symbol::local("a", loc), Symbol::local("b", loc)],
            &[Statement::assign("a", Expression::number("42", loc), loc)],
            loc,
        );
        let res = blk.splat_blocks().unwrap();
        assert_eq!(
            res.locals,
            vec![Symbol::local("a", loc), Symbol::local("b", loc)],
        );
        assert_eq!(
            res.stmnts,
            vec![Statement::assign("a", Expression::number("42", loc), loc)],
        );
        let blk = Block::block(
            &[Symbol::local("c", loc)],
            &[
                Statement::assign("c", Expression::number("23", loc), loc),
                Statement::block(blk),
            ],
            loc,
        );
        let res = blk.splat_blocks().unwrap();
        assert_eq!(
            res.locals,
            vec![
                Symbol::local("c", loc),
                Symbol::local("a", loc),
                Symbol::local("b", loc)
            ],
        );
        assert_eq!(
            res.stmnts,
            vec![
                Statement::assign("c", Expression::number("23", loc), loc),
                Statement::assign("a", Expression::number("42", loc), loc)
            ],
        );
        let blk = Block::block(&[], &[Statement::block(blk)], loc);
        let res = blk.splat_blocks().unwrap();
        assert_eq!(
            res.locals,
            vec![
                Symbol::local("c", loc),
                Symbol::local("a", loc),
                Symbol::local("b", loc)
            ],
        );
        assert_eq!(
            res.stmnts,
            vec![
                Statement::assign("c", Expression::number("23", loc), loc),
                Statement::assign("a", Expression::number("42", loc), loc)
            ],
        );

        let blk = Block::block(
            &[Symbol::local("a", loc), Symbol::local("b", loc)],
            &[
                Statement::assign("a", Expression::number("42", loc), loc),
                Statement::block(Block::block(
                    &[Symbol::local("a", loc), Symbol::local("b", loc)],
                    &[Statement::assign("b", Expression::number("42", loc), loc)],
                    loc,
                )),
            ],
            loc,
        );

        let res = blk.splat_blocks().unwrap();
        assert_eq!(
            res.locals,
            vec![
                Symbol::local("a", loc),
                Symbol::local("b", loc),
                Symbol::local("a_0", loc),
                Symbol::local("b_0", loc),
            ],
        );
        assert_eq!(
            res.stmnts,
            vec![
                Statement::assign("a", Expression::number("42", loc), loc),
                Statement::assign("b_0", Expression::number("42", loc), loc),
            ],
        );
    }

    #[test]
    fn usage() {
        let loc = Location::default();
        let blk = Block::block(
            &[Symbol::local("a", loc), Symbol::local("b", loc)],
            &[
                Statement::assign(
                    "a",
                    Expression::call("foo", vec![Expression::variable("b", loc)], loc),
                    loc,
                ),
                Statement::call("bar", vec![], loc),
            ],
            loc,
        );
        let res = blk.uses();
        assert!(res.is_called("foo").is_some());
        assert!(res.is_called("bar").is_some());

        let s = Parser::new_from_str(
            "
if (v > 0) {
  x = y
  a = 42
} else {
  x = z + a
}",
        )
        .statement()
        .unwrap();

        eprintln!("{s:?}");

        let res = s.uses();
        assert!(res.is_read("v").is_some());
        assert!(res.is_read("x").is_none());
        assert!(res.is_read("y").is_some());
        assert!(res.is_read("z").is_some());
        assert!(res.is_written("y").is_none());
        assert!(res.is_written("z").is_none());
        assert!(res.is_written("a").is_some());
        assert!(res.is_written("x").is_some());
    }
}
