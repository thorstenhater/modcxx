// Some AST rewriters for algebraic simplification.

use rug::{ops::Pow, Float, Rational};

use crate::{
    ast::FUNCTIONS,
    err::{ModcxxError, Result},
    exp::{
        self, Block, BlockT, Callable, Expression, ExpressionT, Operator, Statement, StatementT,
        MAX_PRECISION,
    },
    usr::Uses,
    Map,
};

pub trait Simplify: Sized {
    fn simplify(&self) -> Result<Self>;
}

impl Simplify for Expression {
    fn simplify(&self) -> Result<Self> {
        let mut res = factorize(&self)?;
        loop {
            let new = reduce_algebraic(&res)?;
            if res.equivalent(&new) {
                break;
            }
            res = new;
        }
        // res = collect_terms(&res)?;
        Ok(res)
    }
}

impl Simplify for Block {
    fn simplify(&self) -> Result<Self> {
        let mut res = self.clone();
        res.data = self.data.simplify()?;
        Ok(res)
    }
}

impl Simplify for BlockT {
    fn simplify(&self) -> Result<Self> {
        enum VarState {
            Unknown,
            Value(Rational),
            Alias(String),
        }
        let mut known: Map<String, Vec<VarState>> = Map::new();
        let mut res = self.clone();
        for stmnt in res.stmnts.iter_mut() {
            *stmnt = stmnt.simplify()?;
            match &mut stmnt.data {
                StatementT::For(i, _, s, b) => {
                    let bus = b.uses();
                    let ius = i.uses();
                    let sus = s.uses();
                    for (k, vs) in known.iter_mut() {
                        if bus.is_written(k).is_some()
                            || sus.is_written(k).is_some()
                            || ius.is_written(k).is_some()
                        {
                            vs.push(VarState::Unknown);
                        }
                    }
                }
                StatementT::While(_, b) => {
                    let bus = b.uses();
                    for (k, vs) in known.iter_mut() {
                        if bus.is_written(k).is_some() {
                            vs.push(VarState::Unknown);
                        }
                    }
                }
                StatementT::IfThenElse(_, t, e) => {
                    let tus = t.uses();
                    let eus = e.as_ref().map(|e| e.uses()).unwrap_or_default();
                    for (k, vs) in known.iter_mut() {
                        if eus.is_written(k).is_some() || tus.is_written(k).is_some() {
                            vs.push(VarState::Unknown);
                        }
                    }
                }
                StatementT::Assign(lhs, ref mut rhs) => {
                    *rhs = rhs.substitute_if(&mut |ex| match &ex.data {
                        ExpressionT::Variable(v) => {
                            if let Some(x) = known.get(v) {
                                match x.last() {
                                    Some(VarState::Alias(y)) => {
                                        Some(Expression::variable(y, ex.loc))
                                    }
                                    Some(VarState::Value(y)) => Some(Expression::float(y, ex.loc)),
                                    _ => None,
                                }
                            } else {
                                None
                            }
                        }
                        _ => None,
                    })?;
                    match &rhs.data.clone() {
                        ExpressionT::Variable(v) => {
                            let new = if let Some(vs) = known.get(v).as_ref() {
                                match vs.last() {
                                    Some(VarState::Alias(x)) => {
                                        *rhs = Expression::variable(x, stmnt.loc);
                                        VarState::Alias(x.clone())
                                    }
                                    Some(VarState::Value(x)) => {
                                        *rhs = Expression::float(x, stmnt.loc);
                                        VarState::Value(x.clone())
                                    }
                                    _ => VarState::Alias(v.clone()),
                                }
                            } else {
                                VarState::Alias(v.clone())
                            };
                            known.entry(lhs.to_string()).or_default().push(new);
                        }
                        ExpressionT::Number(v) => {
                            known
                                .entry(lhs.to_string())
                                .or_default()
                                .push(VarState::Value(v.clone()));
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
            // TODO: _do_ something with the known items here.
            // NOTE: take care with shadowing!
            // NOTE: is shadowing even allowed?
        }
        Ok(res)
    }
}

/// Collect terms into powers of a base
pub(crate) fn collect_terms(expr: &Expression, base: &str) -> Result<(isize, Expression)> {
    // split off a power of base from expression. return reduced expression and
    // the exponent of base in the original expression
    fn go(expr: &Expression, base: &str) -> (isize, Expression) {
        let loc = expr.loc;
        match &expr.data {
            ExpressionT::Variable(v) if v == base => (1, Expression::number("1", expr.loc)),
            ExpressionT::Unary(op, ex) => match op {
                Operator::Neg => {
                    let (e, r) = go(ex, base);
                    (e, Expression::unary(*op, r, loc))
                }
                _ => unreachable!(),
            },
            ExpressionT::Binary(op, lhs, rhs) => match op {
                Operator::Add | Operator::Sub => {
                    let (el, rl) = go(lhs, base);
                    let (er, rr) = go(rhs, base);
                    if el == er {
                        (el, Expression::binary(rl, *op, rr, loc))
                    } else if el > er {
                        let res = Expression::binary(
                            Expression::mul(
                                Expression::pow(
                                    Expression::variable(&base, loc),
                                    Expression::float(el - er, loc),
                                    loc,
                                ),
                                rl,
                                loc,
                            ),
                            *op,
                            rr,
                            loc,
                        );
                        (er, res)
                    } else {
                        let res = Expression::binary(
                            rl,
                            *op,
                            Expression::mul(
                                Expression::pow(
                                    Expression::variable(&base, loc),
                                    Expression::float(er - el, loc),
                                    loc,
                                ),
                                rr,
                                loc,
                            ),
                            loc,
                        );
                        (el, res)
                    }
                }
                Operator::Mul => {
                    let (el, rl) = go(lhs, base);
                    let (er, rr) = go(rhs, base);
                    (el + er, Expression::binary(rl, *op, rr, loc))
                }
                Operator::Div => {
                    let (el, rl) = go(lhs, base);
                    let (er, rr) = go(rhs, base);
                    (el - er, Expression::binary(rl, *op, rr, loc))
                }
                _ => (0, expr.clone()),
            },
            _ => (0, expr.clone()),
        }
    }
    Ok(go(expr, base))
}

fn reduce_algebraic(exp: &Expression) -> Result<Expression> {
    use ExpressionT::*;
    use Operator::*;
    let res = exp.clone();
    let loc = exp.loc;
    match &res.data {
        Binary(op, l, r) => {
            let l = reduce_algebraic(l)?;
            let r = reduce_algebraic(r)?;
            match op {
                Mul => {
                    match (&l.data, &r.data) {
                        // Trivial identities
                        (Number(n), Number(m)) => {
                            return Ok(Expression::float(n * m, loc));
                        }
                        (Number(n), _) if n == &-1 => return Ok(Expression::neg(r, loc)),
                        (_, Number(n)) if n == &-1 => return Ok(Expression::neg(l, loc)),
                        (Number(n), _) if n == &1 => {
                            return Ok(r);
                        }
                        (_, Number(n)) if n == &1 => {
                            return Ok(l);
                        }
                        (Number(n), _) if n == &0 => return Ok(Expression::float(0, loc)),
                        (_, Number(n)) if n == &0 => return Ok(Expression::float(0, loc)),
                        // Collect into larger fractions
                        (Binary(Div, n, d), _) => {
                            let n = reduce_algebraic(&Expression::mul(r, *n.clone(), loc))?;
                            return Ok(Expression::div(n, *d.clone(), loc));
                        }
                        (_, Binary(Div, n, d)) => {
                            let n = reduce_algebraic(&Expression::mul(l, *n.clone(), loc))?;
                            return Ok(Expression::div(n, *d.clone(), loc));
                        }
                        (x, Binary(Pow, y, n)) if x.equivalent(y) => {
                            return Ok(Expression::pow(
                                l,
                                Expression::add(*n.clone(), Expression::float(1, loc), loc),
                                loc,
                            ))
                        }
                        // Float out negation
                        (Unary(Neg, x), _) => {
                            return Ok(Expression::neg(Expression::mul(*x.clone(), r, loc), loc))
                        }
                        (_, Unary(Neg, r)) => {
                            return Ok(Expression::neg(Expression::mul(l, *r.clone(), loc), loc))
                        }
                        _ => {}
                    }
                    if r < l {
                        return Ok(Expression::mul(r, l, loc));
                    } else {
                        return Ok(Expression::mul(l, r, loc));
                    }
                }
                Div => {
                    match (&l.data, &r.data) {
                        (x, y) if x.equivalent(y) => return Ok(Expression::float(1, loc)),
                        (Number(n), Number(m)) => return Ok(Expression::float(n / m, loc)),
                        (Number(n), _) if n == &0 => return Ok(Expression::float(0, loc)),
                        (_, Number(n)) if n == &0 => {
                            return Err(ModcxxError::InternalError("Division by zero".to_string()))
                        }
                        (_, Number(n)) if n == &1 => return Ok(l),
                        (_, Number(n)) if n == &-1 => return Ok(Expression::neg(l, loc)),
                        (_, Number(n)) => {
                            return Ok(Expression::mul(Expression::float(1 / n, loc), l, loc))
                        }
                        (Unary(Neg, l), _) => {
                            return Ok(Expression::neg(Expression::div(*l.clone(), r, loc), loc))
                        }
                        (_, Unary(Neg, r)) => {
                            return Ok(Expression::neg(Expression::div(l, *r.clone(), loc), loc))
                        }
                        // (a/b)/r => a/ (b r)
                        (Binary(Div, n, d), _) => {
                            return Ok(Expression::div(
                                *n.clone(),
                                Expression::mul(*d.clone(), r, l.loc),
                                loc,
                            ))
                        }
                        // l/(a/b) => l b / a
                        (_, Binary(Div, n, d)) => {
                            return Ok(Expression::div(
                                Expression::mul(l, *d.clone(), loc),
                                *n.clone(),
                                loc,
                            ))
                        }
                        _ => {}
                    }
                }
                Add => {
                    if r < l {
                        return Ok(Expression::add(r, l, loc));
                    }
                    match (&l.data, &r.data) {
                        (Number(n), Number(m)) => return Ok(Expression::float(n + m, loc)),
                        (Number(n), _) if n == &0 => return Ok(r),
                        (_, Number(n)) if n == &0 => return Ok(l),
                        (Unary(Neg, l), Unary(Neg, r)) => {
                            return Ok(Expression::neg(
                                Expression::add(*l.clone(), *r.clone(), loc),
                                loc,
                            ))
                        }
                        (Unary(Neg, l), _) => {
                            return Ok(Expression::sub(r.clone(), *l.clone(), loc))
                        }
                        (_, Unary(Neg, r)) => {
                            return Ok(Expression::sub(l.clone(), *r.clone(), loc))
                        }
                        _ => {}
                    }
                    if r < l {
                        return Ok(Expression::add(r, l, loc));
                    } else {
                        return Ok(Expression::add(l, r, loc));
                    }
                }
                Sub => match (&l.data, &r.data) {
                    (x, y) if x.equivalent(y) => return Ok(Expression::float(0, loc)),
                    (Number(n), Number(m)) => return Ok(Expression::float(n - m, loc)),
                    (Number(n), _) if n == &0 => return Ok(Expression::neg(r, loc)),
                    (_, Number(n)) if n == &0 => return Ok(l),
                    (Unary(Neg, l), Unary(Neg, r)) => {
                        return Ok(Expression::sub(*r.clone(), *l.clone(), loc))
                    }
                    (Unary(Neg, l), _) => {
                        return Ok(Expression::neg(
                            Expression::add(*l.clone(), r.clone(), loc),
                            loc,
                        ))
                    }
                    (_, Unary(Neg, r)) => return Ok(Expression::add(l.clone(), *r.clone(), loc)),
                    _ => {}
                },
                Pow => match (&l.data, &r.data) {
                    (Number(n), Number(m)) => {
                        let lf = Float::with_val(MAX_PRECISION, n);
                        let rf = Float::with_val(MAX_PRECISION, m);
                        return Ok(Expression::float(lf.pow(rf).to_rational().unwrap(), loc));
                    }
                    (Number(n), _) if n == &0 => return Ok(Expression::float(0, loc)),
                    (Number(n), _) if n == &1 => return Ok(Expression::float(1, loc)),
                    (_, Number(n)) if n == &0 => return Ok(Expression::float(1, loc)),
                    (_, Number(n)) if n == &1 => return Ok(l.clone()),
                    _ => {}
                },
                LT => {
                    if let (Number(n), Number(m)) = (&l.data, &r.data) {
                        return Ok(Expression::float((n < m) as i64, loc));
                    }
                }
                GT => {
                    if let (Number(n), Number(m)) = (&l.data, &r.data) {
                        return Ok(Expression::float((n > m) as i64, loc));
                    }
                }
                GE | LE | Eq if l.equivalent(&r) => return Ok(Expression::float(1, loc)),
                NEq if l.equivalent(&r) => return Ok(Expression::float(0, loc)),
                GE => {
                    if let (Number(n), Number(m)) = (&l.data, &r.data) {
                        return Ok(Expression::float((n >= m) as i64, loc));
                    }
                }
                LE => {
                    if let (Number(n), Number(m)) = (&l.data, &r.data) {
                        return Ok(Expression::float((n <= m) as i64, loc));
                    }
                }
                And => match (&l.data, &r.data) {
                    (Number(n), Number(m)) => {
                        return Ok(Expression::float((n != &0 && m != &0) as i64, loc))
                    }
                    (Number(n), _) if n == &0 => return Ok(Expression::float(0, loc)),
                    (_, Number(n)) if n == &0 => return Ok(Expression::float(0, loc)),
                    (Number(n), _) if n == &1 => return Ok(r),
                    (_, Number(n)) if n == &1 => return Ok(l),
                    (a, b) if a.equivalent(b) => return Ok(l),
                    _ => {}
                },
                Or => match (&l.data, &r.data) {
                    (Number(n), _) if n == &1 => return Ok(Expression::float(1, loc)),
                    (_, Number(n)) if n == &1 => return Ok(Expression::float(1, loc)),
                    (Number(n), _) if n == &0 => return Ok(r),
                    (_, Number(n)) if n == &0 => return Ok(l),
                    (a, b) if a.equivalent(b) => return Ok(l),
                    _ => {}
                },
                _ => {}
            }
            return Ok(Expression::binary(l, *op, r, loc));
        }
        Unary(op, y) => {
            let x = reduce_algebraic(y)?;
            match op {
                Neg => match &x.data {
                    ExpressionT::Binary(Sub, l, r) => {
                        return Ok(Expression::sub(*r.clone(), *l.clone(), x.loc))
                    }
                    ExpressionT::Unary(Neg, r) => return Ok(*r.clone()),
                    ExpressionT::Number(v) => return Ok(Expression::float(-v, loc)),
                    _ => {}
                },
                Not => match &x.data {
                    ExpressionT::Number(v) if v == &0 => return Ok(Expression::float(1, loc)),
                    ExpressionT::Number(_) => return Ok(Expression::float(0, loc)),
                    _ => {}
                },
                _ => {}
            }
            return Ok(Expression::unary(*op, x, loc));
        }
        Call(f, args) => {
            let args = args
                .iter()
                .map(reduce_algebraic)
                .collect::<Result<Vec<_>>>()?;
            if let Some((_, arity)) = FUNCTIONS.iter().find(|b| b.0 == f) {
                if *arity != args.len() {
                    return Err(ModcxxError::InternalError(format!("Built-in function '{f}' called with {} args, but requires exactly {arity}.", args.len())));
                }
                if args
                    .iter()
                    .all(|v| matches!(v.data, exp::ExpressionT::Number(_)))
                {
                    let args = args
                        .iter()
                        .map(|arg| {
                            let ExpressionT::Number(x) = &arg.data else {
                                unreachable!();
                            };
                            Float::with_val(MAX_PRECISION, x)
                        })
                        .collect::<Vec<_>>();
                    match f.as_ref() {
                        "exp" => {
                            return Ok(Expression::float(
                                args[0].clone().exp().to_rational().unwrap(),
                                loc,
                            ));
                        }
                        "sin" => {
                            return Ok(Expression::float(
                                args[0].clone().sin().to_rational().unwrap(),
                                loc,
                            ));
                        }
                        "cos" => {
                            return Ok(Expression::float(
                                args[0].clone().cos().to_rational().unwrap(),
                                loc,
                            ));
                        }
                        "log" => {
                            return Ok(Expression::float(
                                args[0].clone().ln().to_rational().unwrap(),
                                loc,
                            ));
                        }
                        "log10" => {
                            return Ok(Expression::float(
                                args[0].clone().log10().to_rational().unwrap(),
                                loc,
                            ));
                        }
                        "exprelr" => {
                            return Ok(Expression::float(
                                1 / args[0].clone().exp_m1().to_rational().unwrap(),
                                loc,
                            ));
                        }
                        "max" => {
                            return Ok(Expression::float(
                                args[0].clone().max(&args[1]).to_rational().unwrap(),
                                loc,
                            ));
                        }
                        "min" => {
                            return Ok(Expression::float(
                                args[0].clone().min(&args[1]).to_rational().unwrap(),
                                loc,
                            ));
                        }
                        _ => unreachable!(""),
                    }
                }
            }
            return Ok(Expression::call(f, args, loc));
        }
        _ => {}
    }
    Ok(res)
}

/// helper to tack a series of multiplications onto an expression
fn add_factors(exp: &Expression, cfs: &[ExpressionT]) -> Result<Expression> {
    let mut exp = reduce_algebraic(exp)?;
    let loc = exp.loc;
    for cf in cfs {
        let cf = Expression {
            data: cf.clone(),
            loc,
        };
        let cf = reduce_algebraic(&cf)?;

        if let ExpressionT::Number(v) = &cf.data {
            if v == &0 {
                return Ok(Expression::float(0, loc));
            }
            if v == &1 {
                continue;
            }
        }
        exp = reduce_algebraic(&Expression::mul(cf.clone(), exp, loc))?;
    }
    reduce_algebraic(&exp)
}

/// recursively factorize expression and return a list of common factors and the
/// original expression stripped of that factors
fn factorize(exp: &Expression) -> Result<Expression> {
    fn go(exp: &Expression) -> Result<(Vec<ExpressionT>, Expression)> {
        use Operator::*;
        let loc = exp.loc;
        match &exp.data {
            ExpressionT::Unary(op, rhs) => {
                let (cfs, rhs) = go(rhs)?;
                Ok((cfs, Expression::unary(*op, rhs, loc)))
            }
            ExpressionT::Binary(op, lhs, rhs) => {
                let (mut rfs, mut rhs) = go(rhs)?;
                let (mut lfs, mut lhs) = go(lhs)?;
                match op {
                    // Powers are factors on their own
                    Pow => Ok((
                        vec![
                            Expression::binary(
                                add_factors(&lhs, &lfs)?,
                                *op,
                                add_factors(&rhs, &rfs)?,
                                loc,
                            )
                            .data,
                        ],
                        Expression::float(1, loc),
                    )),
                    // Addition
                    // Factors: intersection of left and right.
                    // Left:    stripped left times the factors not common
                    // Right:   stripped right times the factors not common
                    Add | Sub => {
                        let mut cfs = Vec::new();
                        for l in &lfs {
                            if rfs.contains(l) {
                                cfs.push(l.clone());
                            }
                        }
                        lfs.retain(|x| !cfs.contains(x));
                        lhs = add_factors(&lhs, &lfs)?;
                        rfs.retain(|x| !cfs.contains(x));
                        rhs = add_factors(&rhs, &rfs)?;
                        Ok((cfs, Expression::binary(lhs, *op, rhs, loc)))
                    }
                    // Multiplication
                    // Factors: union of left and right.
                    // Left:    stripped left
                    // Right:   stripped right
                    Mul => {
                        let mut cfs = Vec::new();
                        cfs.append(&mut rfs);
                        cfs.append(&mut lfs);
                        Ok((cfs, Expression::binary(lhs, *op, rhs, loc)))
                    }
                    // Division
                    // Factors: left factors - right factors
                    // Left:    stripped left
                    // Right:   stripped right * (right factors - left factors)
                    // Thus factors common between left and right are reduced
                    Div => {
                        let mut cfs = Vec::new();
                        for l in &lfs {
                            if let Some(ix) = rfs.iter().position(|r| l.equivalent(r)) {
                                rfs.swap_remove(ix);
                            } else {
                                cfs.push(l.clone());
                            }
                        }
                        rfs.retain(|x| !cfs.contains(x) && !lfs.contains(x));
                        rhs = add_factors(&rhs, &rfs)?;
                        Ok((cfs, Expression::binary(lhs, *op, rhs, loc)))
                    }
                    LT | GT | GE | LE | Eq | NEq | And | Or => Ok((
                        Vec::new(),
                        Expression::binary(
                            add_factors(&lhs, &lfs)?,
                            *op,
                            add_factors(&rhs, &rfs)?,
                            loc,
                        ),
                    )),
                    _ => Err(ModcxxError::InternalError(format!(
                        "No clue how to factorize over binary operator {op}"
                    ))),
                }
            }
            ExpressionT::Number(v) if v != &1 => {
                Ok((vec![exp.data.clone()], Expression::float(1, loc)))
            }
            ExpressionT::Variable(_) => Ok((vec![exp.data.clone()], Expression::float(1, loc))),
            _ => Ok((Vec::new(), exp.clone())),
        }
    }
    let (cfs, exp) = go(exp)?;
    let exp = add_factors(&exp, &cfs)?;
    Ok(exp)
}

impl Simplify for Statement {
    fn simplify(&self) -> Result<Self> {
        let mut res = self.clone();
        use StatementT::*;
        match &mut res.data {
            Assign(_, rhs) => *rhs = rhs.simplify()?,
            Initial(blk) | Block(blk) => *blk = blk.simplify()?,
            Rate(l, r, f, b) => {
                *l = l.simplify()?;
                *r = r.simplify()?;
                *f = f.simplify()?;
                *b = b.simplify()?;
            }
            Conserve(lhs, rhs) | Linear(lhs, rhs) => {
                *lhs = lhs.simplify()?;
                *rhs = rhs.simplify()?;
            }
            Derivative(_, rhs) => {
                *rhs = rhs.simplify()?;
            }
            Return(rhs) => *rhs = rhs.simplify()?,
            IfThenElse(c, t, e) => {
                *c = c.simplify()?;
                *t = t.simplify()?;
                if let Some(e) = e {
                    *e = e.simplify()?;
                }
            }
            Call(_, ref mut args) => {
                for ex in args.iter_mut() {
                    *ex = ex.simplify()?;
                }
            }
            Solve(_, _) => {}
            For(i, c, s, b) => {
                *i = Box::new(i.simplify()?);
                *c = c.simplify()?;
                *s = Box::new(s.simplify()?);
                *b = b.simplify()?;
            }
            While(c, b) => {
                *c = c.simplify()?;
                *b = b.simplify()?;
            }
        }
        Ok(res)
    }
}

impl Simplify for Callable {
    fn simplify(&self) -> Result<Self> {
        let mut res = self.clone();
        res.body = res.body.simplify()?;
        Ok(res)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::exp::Rational;
    use crate::loc::Location;

    #[test]
    fn test_mul() {
        let ex = Expression::mul(
            Expression::number("1", Location::default()),
            Expression::number("42", Location::default()),
            Location::default(),
        );
        assert_eq!(
            ex.simplify().unwrap(),
            Expression::number("42", Location::default())
        );

        let ex = Expression::mul(
            Expression::number("2", Location::default()),
            Expression::number("42", Location::default()),
            Location::default(),
        );
        assert_eq!(
            ex.simplify().unwrap(),
            Expression::number("84", Location::default())
        );

        let ex = Expression::add(
            Expression::mul(
                Expression::number("1", Location::default()),
                Expression::number("42", Location::default()),
                Location::default(),
            ),
            Expression::mul(
                Expression::number("1", Location::default()),
                Expression::number("42", Location::default()),
                Location::default(),
            ),
            Location::default(),
        );
        assert_eq!(
            ex.simplify().unwrap(),
            Expression::number("84", Location::default()),
        );

        let ex = Statement::assign(
            "X",
            Expression::mul(
                Expression::number("1", Location::default()),
                Expression::number("42", Location::default()),
                Location::default(),
            ),
            Location::default(),
        );

        assert_eq!(
            ex.simplify().unwrap(),
            Statement::assign(
                "X",
                Expression::number("42", Location::default()),
                Location::default()
            ),
        );

        let ex = Block::block(
            &[],
            &[Statement::assign(
                "X",
                Expression::mul(
                    Expression::number("1", Location::default()),
                    Expression::number("42", Location::default()),
                    Location::default(),
                ),
                Location::default(),
            )],
            Location::default(),
        );

        assert_eq!(
            ex.simplify().unwrap(),
            Block::block(
                &[],
                &[Statement::assign(
                    "X",
                    Expression::number("42", Location::default()),
                    Location::default()
                ),],
                Location::default()
            )
        );
    }

    #[test]
    fn test_div() {
        // 1/2
        let exp = Expression::div(
            Expression::float(1, Location::new(0, 0, 0)),
            Expression::float(2, Location::new(0, 3, 3)),
            Location::new(0, 1, 1),
        );
        let ex = Expression::number("0.5", Location::new(0, 1, 1));
        assert_eq!(exp.simplify().unwrap(), ex);
        // 1/(2/3)
        let exp = Expression::div(
            Expression::number("1", Location::new(0, 0, 0)),
            Expression::div(
                Expression::number("2", Location::new(0, 3, 3)),
                Expression::number("3", Location::new(0, 5, 5)),
                Location::new(0, 4, 4),
            ),
            Location::new(0, 1, 1),
        );
        assert_eq!(
            exp.simplify().unwrap(),
            Expression::number("1.5", Location::new(0, 1, 1))
        );

        // (1/2)/3 = 1/2/3
        let exp = Expression::div(
            Expression::div(
                Expression::number("1", Location::new(0, 0, 0)),
                Expression::number("2", Location::new(0, 2, 2)),
                Location::new(0, 1, 1),
            ),
            Expression::number("3", Location::new(0, 4, 4)),
            Location::new(0, 3, 3),
        );
        assert_eq!(
            exp.simplify().unwrap(),
            Expression::float(
                Rational::from(1) / Rational::from(6),
                Location::new(0, 3, 3)
            )
        );
    }

    #[test]
    fn test_sub() {
        // 1-2
        let exp = Expression::sub(
            Expression::number("1", Location::new(0, 0, 0)),
            Expression::number("2", Location::new(0, 3, 3)),
            Location::new(0, 1, 1),
        );
        assert_eq!(
            exp.simplify().unwrap(),
            Expression::number("-1", Location::new(0, 1, 1))
        );
        // 1-(2-3)
        let exp = Expression::sub(
            Expression::number("1", Location::new(0, 0, 0)),
            Expression::sub(
                Expression::number("2", Location::new(0, 3, 3)),
                Expression::number("3", Location::new(0, 5, 5)),
                Location::new(0, 4, 4),
            ),
            Location::new(0, 1, 1),
        );
        assert_eq!(
            exp.simplify().unwrap(),
            Expression::number("2", Location::new(0, 1, 1))
        );

        // (1-2)-3 = 1-2-3
        let exp = Expression::sub(
            Expression::sub(
                Expression::number("1", Location::new(0, 0, 0)),
                Expression::number("2", Location::new(0, 2, 2)),
                Location::new(0, 1, 1),
            ),
            Expression::number("3", Location::new(0, 4, 4)),
            Location::new(0, 3, 3),
        );
        assert_eq!(
            exp.simplify().unwrap(),
            Expression::number("-4", Location::new(0, 3, 3))
        );
    }

    #[test]
    fn test_pow() {
        let ex = Expression::pow(
            Expression::number("42", Location::default()),
            Expression::number("1", Location::default()),
            Location::default(),
        );
        assert_eq!(
            ex.simplify().unwrap(),
            Expression::number("42", Location::default())
        );

        let ex = Statement::derivative(
            "X",
            Expression::pow(
                Expression::variable("Y", Location::default()),
                Expression::number("1", Location::default()),
                Location::default(),
            ),
            Location::default(),
        );
        assert_eq!(
            ex.simplify().unwrap(),
            Statement::derivative(
                "X",
                Expression::variable("Y", Location::default()),
                Location::default()
            )
        );

        let ex = Expression::pow(
            Expression::number("2", Location::default()),
            Expression::pow(
                Expression::number("3", Location::default()),
                Expression::number("4", Location::default()),
                Location::default(),
            ),
            Location::default(),
        );
        assert_eq!(
            ex.simplify().unwrap(),
            Expression::number("2417851639229258349412352", Location::default())
        );
    }

    #[test]
    /// Test that neutral elements do not matter after reduction
    fn test_squeeze_ones() {
        use crate::par::Parser;
        let red =
            Parser::new_from_str("---(1 * (2 - 1) * 1 * 1 * (alpha + beta + 0)) / (alpha / 1)")
                .expression()
                .unwrap();
        let red = reduce_algebraic(&red).unwrap();
        let exp = Parser::new_from_str("-(alpha + beta) / alpha")
            .expression()
            .unwrap();
        let exp = reduce_algebraic(&exp).unwrap();
        assert!(exp.equivalent(&red));
        let red = Parser::new_from_str("1 * 1").expression().unwrap();
        let red = red.simplify().unwrap();
        let exp = Parser::new_from_str("1").expression().unwrap();
        let exp = reduce_algebraic(&exp).unwrap();
        assert!(exp.equivalent(&red));
    }

    #[test]
    fn test_factorize() {
        fn test(exp: &str, ok: &Expression) {
            use crate::par::Parser;
            let mut exp = Parser::new_from_str(exp).expression().unwrap();
            loop {
                let new = factorize(&exp).unwrap();
                let new = reduce_algebraic(&new).unwrap();
                if new == exp {
                    break;
                }
                exp = new;
            }
            assert!(exp.equivalent(ok))
        }
        let loc = Location::default();
        test(
            "(2 * x + x)",
            &Expression::mul(
                Expression::float(3, loc),
                Expression::variable("x", loc),
                loc,
            ),
        );
        test(
            "(a * x + b * x)",
            &Expression::mul(
                Expression::add(
                    Expression::variable("b", loc),
                    Expression::variable("a", loc),
                    loc,
                ),
                Expression::variable("x", loc),
                loc,
            ),
        );
        test(
            "(a * x + x * b) / (2*x - x)",
            &Expression::add(
                Expression::variable("b", loc),
                Expression::variable("a", loc),
                loc,
            ),
        );
        test("(a * x + x * b) / (b + a)", &Expression::variable("x", loc));
    }

    #[test]
    fn test_collect() {
        fn test(inp: &str, (pow, out): (isize, &str), base: &str) {
            let inp = crate::par::Parser::new_from_str(inp).expression().unwrap();
            let (exp, inp) = collect_terms(&inp, base).unwrap();
            let inp = inp.simplify().unwrap();
            let out = crate::par::Parser::new_from_str(out).expression().unwrap();
            assert_eq!(exp, pow);
            assert!(out.equivalent(&inp));
        }
        test("x * x", (2, "1"), "x");
        test("x * y + z * x", (1, "y + z"), "x");
        test("x * x * y + z * x", (1, "x * y + z"), "x");
        test("(x + z)/(x * x)", (-2, "x + z"), "x");
    }
}
