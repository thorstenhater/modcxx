use rug::Rational;

use crate::{
    dif::derivative,
    err::Result,
    exp::{Block, Expression, ExpressionT, Statement, StatementT, Symbol},
    loc::Location,
    opt::Simplify,
};

fn solve_linear(lhs: &str, a: Expression, b: Expression, loc: Location) -> Result<Statement> {
    let ba = Statement::assign("ba_", Expression::div(b, a.clone(), loc), loc);
    let sl = Statement::assign(
        lhs,
        Expression::add(
            Expression::neg(Expression::variable("ba_", loc), loc),
            Expression::mul(
                Expression::add(
                    Expression::variable(lhs, loc),
                    Expression::variable("ba_", loc),
                    loc,
                ),
                Expression::call(
                    "exp",
                    vec![Expression::mul(a, Expression::variable("dt", loc), loc)],
                    loc,
                ),
                loc,
            ),
            loc,
        ),
        loc,
    );
    Ok(Statement::block(Block::block(
        &[Symbol::local("ba_", loc)],
        &[ba, sl],
        loc,
    )))
}

fn linearize(lhs: &str, exp: &Expression) -> Result<(Expression, Expression)> {
    let a = exp
        .substitute(
            &ExpressionT::Variable(lhs.to_string()),
            &ExpressionT::Number(Rational::new()),
        )?
        .simplify()?;
    let b = derivative(exp, lhs)?
        .substitute(
            &ExpressionT::Variable(lhs.to_string()),
            &ExpressionT::Number(Rational::new()),
        )?
        .simplify()?;
    let c = derivative(&b, lhs)?
        .substitute(
            &ExpressionT::Variable(lhs.to_string()),
            &ExpressionT::Number(Rational::new()),
        )?
        .simplify()?;
    if !matches!(&c.data, ExpressionT::Number(x) if x.is_zero()) {
        eprintln!("Original {}", crate::nmd::expression(exp)?);
        eprintln!("First    {}", crate::nmd::expression(&b)?);
        eprintln!("Second   {}", crate::nmd::expression(&c)?);
        Err(crate::err::ModcxxError::NonLinear(exp.loc))
    } else {
        Ok((a, b))
    }
}

/// solve Odes using the cnexp method.
/// Preconditions: The set of ODEs must be linear and independent.
/// Thus, we known that
///
///   X' = aX + f(...)
///
/// where X does not appear in the arguments or body of f and we can
/// write
///
///   X' = aX + b
///
/// Then
///
///   X = -b/a + (X + b/a)*exp(a*dt)
///
/// Note though this will be numerically bad for very small
/// (or zero) a. Perhaps re-implement as:
///     s = s + exprel(a*dt)*(s*a+b)*dt
pub fn cnexp(blk: &Block) -> Result<Block> {
    let mut new = Vec::new();
    for stmnt in &blk.stmnts {
        let loc = stmnt.loc;
        let stmnt = match &stmnt.data {
            StatementT::Derivative(lhs, rhs) => {
                let (a, b) = linearize(lhs, rhs)?;
                solve_linear(lhs, a, b, loc)?
            }
            StatementT::IfThenElse(c, t, Some(e)) => {
                Statement::if_then_else(c.clone(), cnexp(t)?, Some(cnexp(e)?), loc)
            }
            StatementT::Block(inner) => Statement::block(cnexp(inner)?),
            _ => stmnt.clone(),
        };
        new.push(stmnt);
    }
    let mut blk = blk.clone();
    blk.stmnts = new;
    Ok(blk)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::par::Parser;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_linearize() {
        let StatementT::Derivative(_, ds) = Parser::new_from_str("X' = a + b* X")
            .statement()
            .unwrap()
            .data
        else {
            unreachable!();
        };
        let (a, b) = linearize("X", &ds).unwrap();
        assert_eq!(
            a,
            Expression::variable(
                "a",
                Location {
                    line: 0,
                    column: 5,
                    position: 5
                }
            )
        );
        assert_eq!(
            b,
            Expression::variable(
                "b",
                Location {
                    line: 0,
                    column: 9,
                    position: 9
                }
            )
        );
    }
}
