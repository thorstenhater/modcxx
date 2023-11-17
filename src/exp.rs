use std::fmt::{self, Debug};
use std::ops::{Deref, DerefMut};

use crate::{err::Result, loc::Location, Map, Set, usr::{Use, Uses}};

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

    fn rename_all(&self, lut: &Map<String, String>) -> Result<Self> {
        let locals = self.locals.iter().map(|l| l.rename_all(lut)).collect::<Result<Vec<_>>>()?;
        let stmnts = self.stmnts.iter().map(|l| l.rename_all(lut)).collect::<Result<Vec<_>>>()?;

        Ok(Self::block(&locals, &stmnts, self.loc))
    }
}

impl Uses for Block {
    fn uses_timeline(&self) -> Map<String, Vec<(Use, Location)>> {
        let mut res: Map<_, Vec<_>> = Map::new();
        let locals = self
            .locals
            .iter()
            .map(|s| s.name.to_string())
            .collect::<Set<_>>();
        for stmnt in &self.stmnts {
            for (k, mut vs) in stmnt.uses_timeline().into_iter() {
                if !locals.contains(&k) {
                    res.entry(k).or_default().append(&mut vs);
                }
            }
        }
        res
    }
}

pub type Statement = WithLocation<StatementT>;

impl Statement {
    pub fn assign(lhs: &str, rhs: Expression, loc: Location) -> Self {
        Statement::new(StatementT::Assign(lhs.to_string(), rhs), loc)
    }

    pub fn initial(block: Block, loc: Location) -> Self {
        Statement::new(StatementT::Initial(block), loc)
    }

    pub fn conserve(lhs: Expression, rhs: Expression, loc: Location) -> Self {
        Statement::new(StatementT::Conserve(lhs, rhs), loc)
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
        Statement::new(StatementT::Call(Expression::call(fun, args, loc)), loc)
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
            StatementT::Call(ref mut ex) => {
                *ex = ex.substitute(from, to)?;
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
            },
            Return(_) => todo!(),
            Conserve(lhs, rhs) => Self::conserve(lhs.rename_all(lut)?, rhs.rename_all(lut)?, self.loc),
            Rate(a, b, c, d) => Self::rate(a.rename_all(lut)?,
                                           b.rename_all(lut)?,
                                           c.rename_all(lut)?,
                                           d.rename_all(lut)?,
                                           self.loc),
            Linear(lhs, rhs) => Self::linear(lhs.rename_all(lut)?, rhs.rename_all(lut)?, self.loc),
            Derivative(lhs, rhs) => {
                let lhs = if let Some(lhs) = lut.get(lhs) {
                    lhs.to_string()
                } else {
                    lhs.to_string()
                };
                let rhs = rhs.rename_all(lut)?;
                Self::derivative(&lhs, rhs, self.loc)
            },
            IfThenElse(c, t, None) => Self::if_then_else(c.rename_all(lut)?,
                                                      t.rename_all(lut)?,
                                                      None,
                                                      self.loc),
            IfThenElse(c, t, Some(e)) => Self::if_then_else(c.rename_all(lut)?,
                                                      t.rename_all(lut)?,
                                                      Some(e.rename_all(lut)?),
                                                      self.loc),
            Block(blk) => Self::block(blk.rename_all(lut)?),
            Call(Expression {data: ExpressionT::Call(nm, args), loc}) => {
                let nm = if let Some(nm) = lut.get(nm) {
                    nm
                } else {
                    nm
                };
                let args = args.iter().map(|a| a.rename_all(lut)).collect::<Result<Vec<_>>>()?;
                Self::call(nm, args, *loc)
            }
            Initial(blk) => Self::initial(blk.rename_all(lut)?, self.loc),
            _ => unreachable!()
        };
        Ok(res)
    }
}

impl Uses for Statement {
    fn uses_timeline(&self) -> Map<String, Vec<(Use, Location)>> {
        let mut res: Map<_, Vec<_>> = Map::new();
        match &self.data {
            StatementT::Linear(lhs, rhs) => {
                for v in lhs
                    .variables()
                    .into_iter()
                    .chain(rhs.variables().into_iter())
                {
                    res.entry(v.to_string())
                       .or_default()
                       .extend([(Use::R, self.loc), (Use::W, self.loc)]);
                }
            }
            StatementT::Assign(lhs, rhs) => {
                for (k, mut us) in rhs.uses_timeline() {
                    res.entry(k.to_string()).or_default().append(&mut us);
                }
                res.entry(lhs.to_string())
                   .or_default()
                   .push((Use::W, self.loc));
            }
            StatementT::Return(rhs) => {
                for (k, mut us) in rhs.uses_timeline() {
                    res.entry(k.to_string()).or_default().append(&mut us);
                }
            }
            StatementT::Call(call) => {
                if let ExpressionT::Call(fun, args) = &call.data {
                    res.entry(fun.to_string())
                       .or_default()
                       .push((Use::CallP(args.len()), self.loc));
                    for arg in args {
                        for var in arg.variables() {
                            res.entry(var.to_string())
                               .or_default()
                               .push((Use::R, self.loc));
                        }
                    }
                }
            }
            StatementT::Initial(blk) | StatementT::Block(blk) => {
                let locals = blk
                    .locals
                    .iter()
                    .map(|s| s.name.to_string())
                    .collect::<Set<_>>();
                for (k, mut vs) in blk.uses_timeline().into_iter() {
                    if locals.contains(&k) {
                        continue;
                    }
                    res.entry(k).or_default().append(&mut vs);
                }
            }
            StatementT::Conserve(l, r) => {
                for var in l.variables() {
                    res.entry(var.to_string())
                       .or_default()
                       .push((Use::R, self.loc));
                    res.entry(var.to_string())
                       .or_default()
                       .push((Use::W, self.loc));
                }
                for var in r.variables() {
                    res.entry(var.to_string())
                       .or_default()
                       .push((Use::R, self.loc));
                    res.entry(var.to_string())
                       .or_default()
                       .push((Use::W, self.loc));
                }
            }
            StatementT::Rate(l, r, f, b) => {
                for var in l.variables() {
                    res.entry(var.to_string())
                       .or_default()
                       .push((Use::R, self.loc));
                    res.entry(var.to_string())
                       .or_default()
                       .push((Use::W, self.loc));
                }
                for var in r.variables() {
                    res.entry(var.to_string())
                       .or_default()
                       .push((Use::R, self.loc));
                    res.entry(var.to_string())
                       .or_default()
                       .push((Use::W, self.loc));
                }
                for var in f.variables() {
                    res.entry(var.to_string())
                       .or_default()
                       .push((Use::R, self.loc));
                }
                for var in b.variables() {
                    res.entry(var.to_string())
                       .or_default()
                       .push((Use::R, self.loc));
                }
            }
            StatementT::Derivative(nm, ex) => {
                for (v, ref mut u) in ex.uses_timeline().into_iter() {
                    res.entry(v)
                       .or_default()
                       .append(u);
                }
                res.entry(format!("{nm}'"))
                   .or_default()
                   .push((Use::W, self.loc));
            }
            StatementT::IfThenElse(c, t, e) => {
                for (var, us) in c.uses_timeline().iter_mut() {
                    res.entry(var.to_string()).or_default().append(us);
                }
                let ls = t.uses_timeline();
                let rs = if let Some(o) = e {
                    o.uses_timeline()
                } else {
                    Default::default()
                };
                for key in ls.keys().chain(rs.keys()) {
                    let entry = res.entry(key.to_string()).or_default();
                    if let Some(l) = ls.get(key) {
                        if let Some(r) = rs.get(key) {
                            // Both exist...
                            // ...but they are identical:
                            if l.iter().zip(r.iter()).all(|(p, q)| p.0 == q.0) {
                                entry.extend(l.iter());
                            }
                            // ...but history is already muddled:
                            else if l.iter().any(|p| p.0 == Use::Unknown) || r.iter().any(|p| p.0 == Use::Unknown) {
                                entry.push((Use::Unknown, self.loc));
                            }
                            else {
                                entry.push((Use::Unknown, self.loc));
                            }
                        } else {
                            // left is the only thing
                            entry.extend(l.iter());
                        }
                    } else {
                        if let Some(r) = rs.get(key) {
                            // right is the only thing
                            entry.extend(r.iter());
                        } else {
                            unreachable!();
                        }
                    }
                }
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

pub type Solve = WithLocation<(String, SolveT)>;

impl Solve {
    pub fn solve_default(lhs: &str, loc: Location) -> Self {
        Solve { data: (lhs.to_string(), SolveT::Default), loc }
    }

    pub fn solve(lhs: &str, m: &str, loc: Location) -> Self {
        Solve { data: (lhs.to_string(), SolveT::Method(m.to_string())), loc }
    }

    pub fn steadystate(lhs: &str, m: &str, loc: Location) -> Self {
        Solve { data: (lhs.to_string(), SolveT::SteadyState(m.to_string())), loc }
    }
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
    Call(Expression), // This feels redundant
    Initial(Block),   // This is _only_ ever for NET_RECEIVE... I hate NMODL
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

    pub fn neg(rhs: Expression, loc: Location) -> Self {
        Expression::new(ExpressionT::Unary(Operator::Neg, Box::new(rhs)), loc)
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

    pub fn number(var: &str, loc: Location) -> Self {
        Expression::new(ExpressionT::Number(var.to_string()), loc)
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

    pub fn rename_all(&self, lut: &Map<String, String>) -> Result<Self> {
        use ExpressionT::*;
        let res = match &self.data {
            Unary(op, ex) => Self::unary(*op, ex.rename_all(lut)?, self.loc),
            Binary(lhs, op, rhs) => Self::binary(lhs.rename_all(lut)?,
                                                 *op,
                                                 rhs.rename_all(lut)?,
                                                 self.loc),
            Variable(v) => if let Some(v) = lut.get(v) {
                Self::variable(v, self.loc)
            } else {
                self.clone()
            }
            Number(_) => self.clone(),
            String(_) => self.clone(),
            Call(fun, args) => {
                let args = args.iter().map(|a| a.rename_all(lut)).collect::<Result<Vec<_>>>()?;
                let fun = lut.get(fun).unwrap_or(fun);
                Self::call(fun, args, self.loc)
            }
        };
        Ok(res)
    }
}

impl Uses for Expression {
    fn uses_timeline(&self) -> Map<String, Vec<(Use, Location)>> {
        let mut res: Map<String, Vec<(Use, Location)>> = Map::new();
        match &self.data {
            ExpressionT::Variable(v) => {
                res.entry(v.to_string()).or_default().push((Use::R, self.loc));
            }
            ExpressionT::String(_) | ExpressionT::Number(_) => {}
            ExpressionT::Unary(_, e) => {
                res.append(&mut e.uses_timeline());
            }
            ExpressionT::Binary(l, _, r) => {
                res.append(&mut l.uses_timeline());
                res.append(&mut r.uses_timeline());
            }
            ExpressionT::Call(f, es) => {
                for e in es {
                    res.append(&mut e.uses_timeline());
                }
                res.entry(f.to_string()).or_default().push((Use::CallF(es.len()), self.loc));
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
    Number(String),
    String(String),
    Call(String, Vec<Expression>), // TODO(TH): Maybe it's worth letting arbitrary expression occur in this position?!
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
        let res = if let Some(nm) = new.get(&self.name) {
            let mut new = self.clone();
            new.name = nm.to_string();
            new
        } else {
            self.clone()
        };
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
    pub solves: Vec<Solve>,
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
                solves: Vec::new(),
            },
            loc,
        )
    }

    pub fn headless(name: &str, body: Block, solves: &[Solve], loc: Location) -> Self {
        Callable::new(
            CallableT {
                name: name.to_string(),
                args: None,
                unit: None,
                body,
                solves: solves.to_vec(),
            },
            loc,
        )
    }

    pub fn initial(body: Block, solves: &[Solve], loc: Location) -> Self {
        Self::headless("INITIAL", body, solves, loc)
    }

    pub fn breakpoint(body: Block, solves: &[Solve], loc: Location) -> Self {
        Self::headless("BREAKPOINT", body, solves, loc)
    }

    pub fn kinetic(name: &str, body: Block, loc: Location) -> Self {
        Self::headless(name, body, &[], loc)
    }

    pub fn linear(name: &str, body: Block, loc: Location) -> Self {
        Self::headless(name, body, &[], loc)
    }

    pub fn derivative(name: &str, body: Block, loc: Location) -> Self {
        Self::headless(name, body, &[], loc)
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
                solves: Vec::new(),
            },
            loc,
        )
    }
}

impl Uses for Callable {
    fn uses_timeline(&self) -> Map<String, Vec<(Use, Location)>> {
        let mut res: Map<String, Vec<(Use, Location)>> = Map::new();
        for solve in &self.solves {
            res.entry(solve.data.0.to_string()).or_default().push((Use::Solve, solve.loc));
        }
        let mut bod = self.body.uses_timeline();
        bod.retain(|k, _| {
            !self
                .args
                .as_deref()
                .unwrap_or_default()
                .iter()
                .any(|a| &a.name == k)
        });
        res.append(&mut bod);
        res
    }
}

#[cfg(test)]
mod test {
    use crate::{par::Parser, usr::Inventory};

    use super::*;

    #[test]
    fn splat() {
        let loc = Location::default();
        let blk = Block::block(
            &[Symbol::local("a", loc), Symbol::local("b", loc)],
            &[Statement::assign("a", Expression::number("42", loc), loc),],
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
            &[Statement::assign("a", Expression::number("42", loc), loc),
              Statement::block(Block::block(
                  &[Symbol::local("a", loc), Symbol::local("b", loc)],
                  &[Statement::assign("b", Expression::number("42", loc), loc)],
                  loc,
              ))],
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
        assert_eq!(Some(&Set::from_iter([Use::CallP(0)].iter().cloned())), res.get("bar"));
        assert_eq!(Some(&Set::from_iter([Use::CallF(1)].iter().cloned())), res.get("foo"));

        let s = Parser::new_from_str("
if (v > 0) {
  x = y
  a = 42
} else {
  x = z + a
}").statement().unwrap();

        let mut expected = Inventory::new();

        expected.entry("x".to_string()).or_default().insert(Use::W);
        expected.entry("y".to_string()).or_default().insert(Use::R);
        expected.entry("z".to_string()).or_default().insert(Use::R);
        expected.entry("v".to_string()).or_default().insert(Use::R);
        expected.entry("a".to_string()).or_default().insert(Use::Unknown);

        assert_eq!(s.uses(),
                   expected);
    }
}
