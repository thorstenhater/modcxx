// Some AST rewriters for algebraic simplification.

use rug::{ops::Pow, Assign, Float, Rational};

use crate::{
    ast::FUNCTIONS,
    err::{ModcxxError, Result},
    exp::{
        self, Block, BlockT, Callable, Expression, ExpressionT, Operator, Statement, StatementT,
        MAX_PRECISION,
    },
};

pub trait Simplify: Sized {
    fn simplify(&self) -> Result<Self>;
}

impl Simplify for Expression {
    fn simplify(&self) -> Result<Self> {
        let mut res = self.clone();
        res = reduce_algebraic(&res)?;
        res = factorize(&res)?;
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
        let mut known: Vec<(String, Expression)> = Vec::new();
        let mut res = self.clone();
        for stmnt in res.stmnts.iter_mut() {
            *stmnt = stmnt.simplify()?;
            match &mut stmnt.data {
                StatementT::Assign(lhs, ref mut rhs) => {
                    if let ExpressionT::Variable(v) = &rhs.data {
                        if let Some((_, val)) = known.iter().find(|p| &p.0 == v) {
                            *rhs = val.clone();
                        }
                    }
                    known.push((lhs.clone(), rhs.clone()));
                }
                _ => {}
            }
        }
        Ok(res)
    }
}

fn reduce_algebraic(exp: &Expression) -> Result<Expression> {
    use ExpressionT::*;
    use Operator::*;
    let mut res = exp.clone();
    let loc = exp.loc;
    match &res.data {
        Binary(l, op, r) => {
            let l = reduce_algebraic(l)?;
            let r = reduce_algebraic(r)?;
            if matches!(l.data, Number(_)) && matches!(r.data, Number(_)) {
                let ExpressionT::Number(l) = &l.data else {
                    unreachable!();
                };
                let ExpressionT::Number(r) = &r.data else {
                    unreachable!();
                };
                let res = match *op {
                    Add => l.clone() + r.clone(),
                    Sub => l.clone() - r.clone(),
                    Mul => l.clone() * r.clone(),
                    Div => l.clone() / r.clone(),
                    Pow => {
                        let mut lf = Float::new(MAX_PRECISION);
                        lf.assign(l);
                        let mut rf = Float::new(MAX_PRECISION);
                        rf.assign(r);
                        let res = lf.pow(rf);
                        res.to_rational().unwrap()
                    }
                    LT => Rational::from((l < r) as i64),
                    GT => Rational::from((l > r) as i64),
                    LE => Rational::from((l <= r) as i64),
                    GE => Rational::from((l >= r) as i64),
                    NEq => Rational::from((l != r) as i64),
                    Eq => Rational::from((l == r) as i64),
                    And => Rational::from((l == &0 && r == &0) as i64),
                    Or => Rational::from((l == &0 || r == &0) as i64),
                    _ => unreachable!(),
                };
                return Ok(Expression::float(res, loc));
            }
            match op {
                Mul => {
                    match &l.data {
                        // Float out negation
                        ExpressionT::Unary(Neg, l) => {
                            return Ok(Expression::neg(Expression::mul(*l.clone(), r, loc), loc))
                        }
                        // Evaluate trivial cases
                        Number(n) => {
                            if n == &0 {
                                return Ok(Expression::number("0", loc));
                            }
                            if n == &1 {
                                return Ok(r);
                            }
                        }
                        Binary(n, Div, d) => {
                            let n = reduce_algebraic(n)?;
                            let d = reduce_algebraic(d)?;
                            return Ok(Expression::div(Expression::mul(n, r, loc), d, loc));
                        }
                        // Swaps power to the right, but never swap powers
                        // TODO come up with a concept for ordering powers.
                        Binary(_, Pow, _) if !matches!(&l.data, Binary(_, Pow, _)) => {
                            return Ok(Expression::binary(r, *op, l, loc))
                        }
                        // combine powers of the same base
                        Binary(x, Pow, m) if matches!(&r.data, Binary(y, Pow, _) if x == y) => {
                            if let Binary(y, Pow, n) = &r.data {
                                return Ok(Expression::binary(
                                    *y.clone(),
                                    Pow,
                                    Expression::add(*m.clone(), *n.clone(), loc),
                                    loc,
                                ));
                            } else {
                                unreachable!()
                            }
                        }
                        // combine a * a ^ n => a ^ n+1
                        x if matches!(&r.data, Binary(y, Pow, _) if x == &y.data) => {
                            if let Binary(y, Pow, e) = &r.data {
                                return Ok(Expression::binary(
                                    *y.clone(),
                                    Pow,
                                    Expression::add(*e.clone(), Expression::number("1", loc), loc),
                                    loc,
                                ));
                            } else {
                                unreachable!()
                            }
                        }
                        _ => {}
                    }
                    match &r.data {
                        // Float out negation
                        ExpressionT::Unary(Neg, r) => {
                            let r = reduce_algebraic(r)?;
                            return Ok(Expression::neg(Expression::mul(l, r, loc), loc));
                        }
                        Binary(n, Div, d) => {
                            let n = reduce_algebraic(n)?;
                            let d = reduce_algebraic(d)?;
                            return Ok(Expression::div(Expression::mul(l, n, loc), d, loc));
                        }
                        // Evaluate trivial cases
                        Number(n) => {
                            if n == &0 {
                                return Ok(Expression::number("0", loc));
                            }
                            if n == &1 {
                                return Ok(l);
                            }
                        }
                        _ => {}
                    }
                    return Ok(Expression::binary(l, *op, r, loc));
                }
                Div => {
                    // inverse
                    if l.equivalent(&r) {
                        return Ok(Expression::number("1", loc));
                    }
                    match &l.data {
                        Number(n) if n == &0 => return Ok(Expression::number("0", loc)),
                        ExpressionT::Unary(Neg, l) => {
                            return Ok(Expression::neg(Expression::div(*l.clone(), r, loc), loc))
                        }
                        // (a/b)/r => a/ (b r)
                        ExpressionT::Binary(a, Div, b) => {
                            return Ok(Expression::div(
                                *a.clone(),
                                Expression::mul(*b.clone(), r, l.loc),
                                loc,
                            ))
                        }
                        _ => {}
                    }
                    match &r.data {
                        Number(n) if n == &1 => return Ok(l),
                        Number(n) => {
                            return Ok(Expression::mul(
                                Expression::float(Rational::from(1) / n, r.loc),
                                l,
                                loc,
                            ));
                        }
                        // l/(a/b) => l b / a
                        ExpressionT::Binary(a, Div, b) => {
                            return Ok(Expression::div(
                                Expression::mul(*b.clone(), l.clone(), l.loc),
                                *a.clone(),
                                loc,
                            ))
                        }
                        ExpressionT::Unary(Neg, r) => {
                            return Ok(Expression::neg(Expression::div(l, *r.clone(), loc), loc))
                        }
                        _ => {}
                    }
                    return Ok(Expression::binary(l, *op, r, loc));
                }
                Add => {
                    if matches!(&l.data, Number(n) if n == &0) {
                        return Ok(r);
                    } else if matches!(&r.data, Number(n) if n == &0) {
                        return Ok(l);
                    } else if matches!(&r.data, Unary(Neg, _)) {
                        if let Unary(Neg, n) = r.data {
                            res = Expression::binary(l, Sub, *n, loc);
                        } else {
                            unreachable!()
                        }
                    } else {
                        res = Expression::binary(l, *op, r, loc);
                    }
                }
                Sub => {
                    if l == r {
                        return Ok(Expression::number("0", loc));
                    }
                    if matches!(&l.data, Number(n) if n == &0) {
                        res = Expression::neg(r, loc);
                    } else if matches!(&r.data, Number(n) if n == &0) {
                        res = l;
                    } else if matches!(&r.data, ExpressionT::Unary(Neg, _)) {
                        if let ExpressionT::Unary(Neg, x) = r.data {
                            res = Expression::binary(l, Add, *x, loc);
                        } else {
                            unreachable!()
                        }
                    } else {
                        res = Expression::binary(l, *op, r, loc);
                    }
                }
                Pow => {
                    match &l.data {
                        Number(n) => {
                            if n == &1 {
                                return Ok(Expression::number("1", loc));
                            } else if n == &0 {
                                return Ok(Expression::number("0", loc));
                            }
                        }
                        _ => {}
                    }
                    match &r.data {
                        Number(n) => {
                            if n == &1 {
                                return Ok(l);
                            } else if n == &0 {
                                return Ok(Expression::number("1", loc));
                            } else {
                                return Ok(Expression::binary(l, *op, r, loc));
                            }
                        }
                        _ => {}
                    }
                    return Ok(Expression::binary(l, *op, r, loc));
                }
                _ => {
                    return Ok(Expression::binary(l, *op, r, loc));
                }
            }
        }
        Unary(op, x) => {
            let x = reduce_algebraic(x)?;
            match op {
                Neg => match &x.data {
                    ExpressionT::Binary(l, Sub, r) => {
                        return Ok(Expression::binary(*r.clone(), Sub, *l.clone(), x.loc))
                    }
                    ExpressionT::Unary(Neg, r) => return Ok(*r.clone()),
                    ExpressionT::Number(v) => return Ok(Expression::float(-v, loc)),
                    _ => {}
                },
                _ => {}
            }
            return Ok(Expression::neg(x, loc));
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
fn add_factors(exp: &Expression, cfs: &[ExpressionT]) -> Expression {
    let mut exp = exp.clone();
    let loc = exp.loc;
    for cf in cfs {
        let cf = Expression {
            data: cf.clone(),
            loc,
        };
        let cf = reduce_algebraic(&cf).unwrap();

        if let ExpressionT::Number(v) = &cf.data {
            if v == &0 {
                return Expression::float(0, loc);
            }
            if v == &1 {
                continue;
            }
        }
        exp = Expression::mul(cf, exp, loc);
    }
    reduce_algebraic(&exp).unwrap()
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
            ExpressionT::Binary(lhs, op, rhs) => {
                let (mut rfs, mut rhs) = go(rhs)?;
                let (mut lfs, mut lhs) = go(lhs)?;
                match op {
                    // Powers are factors on their own
                    Pow => Ok((
                        vec![
                            Expression::binary(
                                add_factors(&lhs, &lfs),
                                *op,
                                add_factors(&rhs, &rfs),
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
                        lhs = add_factors(&lhs, &lfs);
                        rfs.retain(|x| !cfs.contains(x));
                        rhs = add_factors(&rhs, &rfs);
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
                        eprintln!("Div {cfs:?} <- {lfs:?} - {rfs:?}");
                        rfs.retain(|x| !cfs.contains(x) && !lfs.contains(x));
                        rhs = add_factors(&rhs, &rfs);
                        Ok((cfs, Expression::binary(lhs, *op, rhs, loc)))
                    }
                    LT | GT | GE | LE | Eq | NEq | And | Or => Ok((
                        Vec::new(),
                        Expression::binary(
                            add_factors(&lhs, &lfs),
                            *op,
                            add_factors(&rhs, &rfs),
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
    let exp = add_factors(&exp, &cfs);
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
}
