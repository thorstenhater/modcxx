use std::fmt::{self, Debug};
use std::ops::{Deref, DerefMut};

use crate::{err::Result, src::Location, Map, Set};

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

    pub fn uses(&self) -> Map<String, Set<Use>> {
        let mut res: Map<_, Set<_>> = Map::new();
        let locals = self
            .locals
            .iter()
            .map(|s| s.name.to_string())
            .collect::<Set<_>>();
        for stmnt in &self.stmnts {
            for (k, mut vs) in stmnt.uses().into_iter() {
                if !locals.contains(&k) {
                    res.entry(k).or_default().append(&mut vs);
                }
            }
        }
        res
    }

    pub fn use_timeline(&self) -> Map<String, Vec<Use>> {
        let mut res: Map<_, Vec<_>> = Map::new();
        let locals = self
            .locals
            .iter()
            .map(|s| s.name.to_string())
            .collect::<Set<_>>();
        for stmnt in &self.stmnts {
            for (k, mut vs) in stmnt.use_timeline().into_iter() {
                if !locals.contains(&k) {
                    res.entry(k).or_default().append(&mut vs);
                }
            }
        }
        res
    }

    pub fn splat_blocks(&self) -> Result<Self> {
        let mut locals = self.locals.clone();
        let mut stmnts = self.stmnts.clone();
        loop {
            let mut new = Vec::new();
            for stmnt in &stmnts {
                if let StatementT::Block(inner) = &stmnt.data {
                    eprintln!(
                        "Inner block at {:?} has LOCAL {:?}",
                        inner.loc,
                        inner
                            .locals
                            .iter()
                            .map(|s| s.name.to_string())
                            .collect::<Vec<_>>()
                    );
                    locals.append(&mut inner.locals.clone());
                    eprintln!(
                        "LOCALS now {:?}",
                        locals
                            .iter()
                            .map(|s| s.name.to_string())
                            .collect::<Vec<_>>()
                    );
                    new.append(&mut inner.stmnts.clone());
                } else {
                    new.push(stmnt.clone());
                }
            }
            if new == stmnts {
                break;
            }
            stmnts = new;
        }
        Ok(Block::block(&locals, &stmnts, self.loc))
    }
}

pub type Statement = WithLocation<StatementT>;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Use {
    R,
    W,
    Solve,
    CallP,
    CallF,
    Unknown, // Might be anything... can happen if we cross an if with different usage
}

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

    pub fn rate(from: String, to: String, fwd: Expression, bwd: Expression, loc: Location) -> Self {
        Statement::new(StatementT::Rate(from, to, fwd, bwd), loc)
    }

    pub fn derivative(lhs: &str, rhs: Expression, loc: Location) -> Self {
        Statement::new(StatementT::Derivative(lhs.to_string(), rhs), loc)
    }

    pub fn solve_default(lhs: &str, loc: Location) -> Self {
        Statement::new(StatementT::Solve(lhs.to_string(), Solver::Default), loc)
    }

    pub fn solve(lhs: &str, m: &str, loc: Location) -> Self {
        Statement::new(
            StatementT::Solve(lhs.to_string(), Solver::Method(m.into())),
            loc,
        )
    }

    pub fn steadystate(lhs: &str, m: &str, loc: Location) -> Self {
        Statement::new(
            StatementT::Solve(lhs.to_string(), Solver::SteadyState(m.to_string())),
            loc,
        )
    }

    pub fn if_then_else(i: Expression, t: Statement, e: Option<Statement>, loc: Location) -> Self {
        Statement::new(StatementT::IfThenElse(i, Box::new(t), e.map(Box::new)), loc)
    }

    pub fn block(block: Block) -> Self {
        Statement::new(StatementT::Block(block.clone()), block.loc)
    }

    pub fn call(fun: &str, args: Vec<Expression>, loc: Location) -> Self {
        Statement::new(StatementT::Call(Expression::call(fun, args, loc)), loc)
    }

    pub fn uses(&self) -> Map<String, Set<Use>> {
        let mut res = Map::new();
        match &self.data {
            StatementT::Assign(lhs, rhs) => {
                res.entry(lhs.to_string())
                    .or_insert_with(Set::new)
                    .insert(Use::W);
                for (k, mut us) in rhs.uses() {
                    res.entry(k.to_string()).or_default().append(&mut us);
                }
            }
            StatementT::Return(rhs) => {
                for (k, mut us) in rhs.uses() {
                    res.entry(k.to_string()).or_default().append(&mut us);
                }
            }
            StatementT::Call(call) => {
                if let ExpressionT::Call(fun, args) = &call.data {
                    res.entry(fun.to_string())
                        .or_insert_with(Set::new)
                        .insert(Use::CallP);
                    for arg in args {
                        for var in arg.variables() {
                            res.entry(var.to_string())
                                .or_insert_with(Set::new)
                                .insert(Use::R);
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
                for (k, mut vs) in blk.uses().into_iter() {
                    if locals.contains(&k) {
                        continue;
                    }
                    res.entry(k).or_default().append(&mut vs);
                }
            }
            StatementT::Conserve(l, r) => {
                for var in l.variables() {
                    res.entry(var.to_string())
                        .or_insert_with(Set::new)
                        .insert(Use::R);
                    res.entry(var.to_string())
                        .or_insert_with(Set::new)
                        .insert(Use::W);
                }
                for var in r.variables() {
                    res.entry(var.to_string())
                        .or_insert_with(Set::new)
                        .insert(Use::R);
                    res.entry(var.to_string())
                        .or_insert_with(Set::new)
                        .insert(Use::W);
                }
            }
            StatementT::Rate(l, r, f, b) => {
                res.entry(l.to_string())
                    .or_insert_with(Set::new)
                    .insert(Use::R);
                res.entry(l.to_string())
                    .or_insert_with(Set::new)
                    .insert(Use::W);
                res.entry(r.to_string())
                    .or_insert_with(Set::new)
                    .insert(Use::R);
                res.entry(r.to_string())
                    .or_insert_with(Set::new)
                    .insert(Use::W);
                for var in f.variables() {
                    res.entry(var.to_string())
                        .or_insert_with(Set::new)
                        .insert(Use::R);
                }
                for var in b.variables() {
                    res.entry(var.to_string())
                        .or_insert_with(Set::new)
                        .insert(Use::R);
                }
            }
            StatementT::Derivative(nm, ex) => {
                res.entry(format!("{nm}'"))
                    .or_insert_with(Set::new)
                    .insert(Use::R);
                res.entry(format!("{nm}'"))
                    .or_insert_with(Set::new)
                    .insert(Use::W);
                for var in ex.variables() {
                    res.entry(var.to_string())
                        .or_insert_with(Set::new)
                        .insert(Use::R);
                }
            }
            StatementT::IfThenElse(c, t, e) => {
                for var in c.variables() {
                    res.entry(var.to_string())
                        .or_insert_with(Set::new)
                        .insert(Use::R);
                }
                res.append(&mut t.uses());
                if let Some(o) = e {
                    res.append(&mut o.uses());
                }
            }
            StatementT::Solve(blk, _) => {
                res.entry(blk.to_string())
                    .or_insert_with(Set::new)
                    .insert(Use::Solve);
            }
        }
        res
    }

    pub fn use_timeline(&self) -> Map<String, Vec<Use>> {
        let mut res: Map<_, Vec<_>> = Map::new();
        match &self.data {
            StatementT::Assign(lhs, rhs) => {
                res.entry(lhs.to_string()).or_default().push(Use::W);
                for (k, mut us) in rhs.use_timeline() {
                    res.entry(k.to_string()).or_default().append(&mut us);
                }
            }
            StatementT::Return(rhs) => {
                for (k, mut us) in rhs.use_timeline() {
                    res.entry(k.to_string()).or_default().append(&mut us);
                }
            }
            StatementT::Call(call) => {
                if let ExpressionT::Call(fun, args) = &call.data {
                    res.entry(fun.to_string()).or_default().push(Use::CallP);
                    for arg in args {
                        for var in arg.variables() {
                            res.entry(var.to_string()).or_default().push(Use::R);
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
                for (k, mut vs) in blk.use_timeline().into_iter() {
                    if locals.contains(&k) {
                        continue;
                    }
                    res.entry(k).or_default().append(&mut vs);
                }
            }
            StatementT::Conserve(l, r) => {
                for var in l.variables() {
                    res.entry(var.to_string()).or_default().push(Use::R);
                    res.entry(var.to_string()).or_default().push(Use::W);
                }
                for var in r.variables() {
                    res.entry(var.to_string()).or_default().push(Use::R);
                    res.entry(var.to_string()).or_default().push(Use::W);
                }
            }
            StatementT::Rate(l, r, f, b) => {
                res.entry(l.to_string()).or_default().push(Use::R);
                res.entry(l.to_string()).or_default().push(Use::W);
                res.entry(r.to_string()).or_default().push(Use::R);
                res.entry(r.to_string()).or_default().push(Use::W);
                for var in f.variables() {
                    res.entry(var.to_string()).or_default().push(Use::R);
                }
                for var in b.variables() {
                    res.entry(var.to_string()).or_default().push(Use::R);
                }
            }
            StatementT::Derivative(nm, ex) => {
                res.entry(format!("{nm}'")).or_default().push(Use::R);
                res.entry(format!("{nm}'")).or_default().push(Use::W);
                for var in ex.variables() {
                    res.entry(var.to_string()).or_default().push(Use::R);
                }
            }
            StatementT::IfThenElse(c, t, e) => {
                for var in c.variables() {
                    res.entry(var.to_string()).or_default().push(Use::R);
                }
                let ls = t.use_timeline();
                let rs = if let Some(o) = e {
                    o.use_timeline()
                } else {
                    Default::default()
                };
                for (k, mut l) in ls.into_iter() {
                    let r = if let Some(r) = rs.get(&k) {
                        r.clone()
                    } else {
                        Default::default()
                    };
                    if l == r {
                        res.entry(k).or_default().append(&mut l);
                    } else {
                        res.entry(k).or_default().push(Use::Unknown);
                    }
                }
            }
            StatementT::Solve(blk, _) => {
                res.entry(blk.to_string()).or_default().push(Use::Solve);
            }
        }
        res
    }

    pub fn substitute(&self, from: &ExpressionT, to: &ExpressionT) -> Result<Self> {
        let mut res = self.clone();
        match res.data {
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
            StatementT::Block(Block {
                data: BlockT { ref mut stmnts, .. },
                ..
            }) => {
                for stmnt in stmnts.iter_mut() {
                    *stmnt = stmnt.substitute(from, to)?;
                }
            }
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
                *t = Box::new(t.substitute(from, to)?);
                if let Some(ref mut i) = e {
                    *i = Box::new(i.substitute(from, to)?)
                }
            }
            StatementT::Initial(_) => {
                unimplemented!()
            }
            StatementT::Rate(ref mut f, ref mut t, ref mut fwd, ref mut bwd) => {
                if let ExpressionT::Variable(x) = &to {
                    if let ExpressionT::Variable(y) = &from {
                        if f == y {
                            *f = x.to_string();
                        }
                        if t == y {
                            *t = x.to_string();
                        }
                    }
                }
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
}
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Solver {
    Default,
    Method(String),
    SteadyState(String),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum StatementT {
    Assign(String, Expression),
    Return(Expression),
    Solve(String, Solver),
    Conserve(Expression, Expression),
    Rate(String, String, Expression, Expression),
    Derivative(String, Expression),
    IfThenElse(Expression, Box<Statement>, Option<Box<Statement>>),
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

    fn guses<T>(&self, on: &mut dyn FnMut(&mut T, Use)) -> Map<String, T>
    where
        T: Default,
    {
        fn uses_<T>(ex: &ExpressionT, res: &mut Map<String, T>, on: &mut dyn FnMut(&mut T, Use))
        where
            T: Default,
        {
            match &ex {
                ExpressionT::Variable(v) => {
                    on(res.entry(v.to_string()).or_default(), Use::R);
                }
                ExpressionT::String(_) | ExpressionT::Number(_) => {}
                ExpressionT::Unary(_, e) => uses_(&e.data, res, on),
                ExpressionT::Binary(l, _, r) => {
                    uses_(&l.data, res, on);
                    uses_(&r.data, res, on);
                }
                ExpressionT::Call(f, es) => {
                    on(res.entry(f.to_string()).or_default(), Use::CallF);
                    for e in es {
                        uses_(&e.data, res, on);
                    }
                }
            }
        }
        let mut res = Map::new();
        uses_(&self.data, &mut res, on);
        res
    }

    pub fn uses(&self) -> Map<String, Set<Use>> {
        self.guses(&mut |set, us| {
            set.insert(us);
        })
    }

    pub fn use_timeline(&self) -> Map<String, Vec<Use>> {
        self.guses(&mut |set, us| {
            set.push(us);
        })
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
}

pub struct SymbolT {
    pub name: String,
    pub unit: Option<Unit>,
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

    pub fn uses(&self) -> Map<String, Set<Use>> {
        let mut res = self.body.uses();
        res.retain(|k, _| {
            !self
                .args
                .as_deref()
                .unwrap_or_default()
                .iter()
                .any(|a| &a.name == k)
        });
        res
    }
}

#[cfg(test)]
mod test {
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
        println!("{:?}", res);
    }
}
