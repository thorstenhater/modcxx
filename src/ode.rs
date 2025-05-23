use rug::Rational;

use crate::{
    dif::derivative,
    err::Result,
    exp::{Block, Expression, ExpressionT, Statement, StatementT, Symbol},
    loc::Location,
    opt::Simplify,
};

/// Semi-Symbolic Solvers for ODE Systems arising in NMODL
///
/// In general, we need to solve a system like this
///     X' = f(X, t)
/// (X is a vector of STATE variables) and make the following observations
/// 1. We need to consider 1st order derivatives only, as we can always lower
///    higher order systems to 1st by adding more rows.
/// 2. f(X, t) cannot depend on t, really, as there's no syntax for it in NMODL
///
/// We split by case; f is
/// a) linear and diagonal: f(X) = aX + b where a, b do not depend on X => See CNEXP
/// b) linear               f(X) = AX + b where A, b do not depend on X => See SPARSE
/// c) non-linear           f(X)
///
/// Many of the systems constructed from KINETIC are stiff, so we need to employ
/// implicit methods.
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
        &[ba.simplify()?, sl.simplify()?],
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
        Err(crate::err::ModcxxError::NonLinear(exp.loc))
    } else {
        Ok((a, b))
    }
}

/// [CNEXP] solve Odes using the cnexp method.
/// Preconditions: The set of ODEs must be linear and independent.
/// Thus, we known that
///
///   X' = aX + b
///
/// Then
///
///   X = -b/a + (X + b/a)*exp(a*dt)
///
/// Note though this will be numerically bad for very small
/// (or zero) a. Perhaps re-implement as:
///     s = s + exprel(a*dt)*(s*a + b)*dt
pub fn cnexp(blk: &Block) -> Result<Block> {
    let mut blk = blk.clone();
    for stmnt in blk.stmnts.iter_mut() {
        let loc = stmnt.loc;
        match &stmnt.data {
            StatementT::Derivative(lhs, rhs) => {
                let (a, b) = linearize(&lhs, &rhs)?;
                *stmnt = solve_linear(&lhs, a, b, loc)?;
            }
            StatementT::IfThenElse(c, t, Some(e)) => {
                *stmnt = Statement::if_then_else(c.clone(), cnexp(t)?, Some(cnexp(e)?), loc)
            }
            StatementT::IfThenElse(c, t, None) => {
                *stmnt = Statement::if_then_else(c.clone(), cnexp(t)?, None, loc)
            }
            StatementT::Block(inner) => *stmnt = Statement::block(cnexp(inner)?),
            _ => {}
        };
    }
    Ok(blk)
}

/// [SPARSE] Solve ODEs using the sparse method.
/// Preconditions: The of ODEs must be linear
/// Thus
///   X' = AX + b
/// write out the backward Euler step
///
///   (X(t + dt) - X(t))/dt       = AX(t + dt) + b
///    X(t + dt)                  = A X(t + dt) dt + b dt + X(t)
///    X(t + dt) - A X(t + dt) dt = b dt + X(t)
///    X(t + dt)(1 - A dt)        = X(t) + b dt
/// This is a linear system (because A is linear) and we can
/// solve it using standard approaches.
///
/// _However_, since NMODL is procedural, this isn't quite as clean.
/// Consider:
///
///   STATE { X Y Z }
///
///   ...
///
///   X' = a * X
///   if (c) {
///     Y' = 23 + Z
///   }
///   else {
///     a = 42
///     Y' = a * X
///   }
///   Z' = a*(X - Y)
///
/// Depending on 'c', 'a' might have different values and we cannot blindly
/// shuffle statements, since 'a' might change values. We also cannot use
/// SSA here, as there is no guarantee that
pub fn sparse(blk: &Block) -> Result<Block> {
    /*
        let mut sys = Vec::new();
        for stmnt in &blk.stmnts {
            // TODO what happens if not all statements for the system are consecutive?
            let loc = stmnt.loc;
            let stmnt = match &stmnt.data {
                StatementT::Derivative(lhs, rhs) => Statement::assign(
                    lhs,
                    Expression::add(
                        Expression::variable(lhs, loc),
                        Expression::mul(Expression::variable("dt", loc), rhs.clone(), loc),
                        loc,
                    ),
                    loc,
                ),
                StatementT::IfThenElse(c, t, e) => {
                    // TODO We _should_ be checking that the inner sparse doesn't
                    // collide with any other that we are currently processing.
                    Statement::if_then_else(c.clone(),
                                            sparse(t)?,
                                            e.as_ref().map(|i| sparse(i)).transpose()?,
                                            loc)
                }
                StatementT::Block(inner) => Statement::block(sparse(inner)?),
                _ => stmnt.clone(),
            };
        }
        let mut blk = blk.clone();
        // blk.stmnts = new;
    */
    todo!()
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
                    column: 10,
                    position: 10,
                }
            )
        );
    }

    #[test]
    fn cnexp_solver() {
        use crate::{ast, par};
        let s = par::parse(
            "
NEURON { SUFFIX test }

INITIAL {}

STATE { s }

BREAKPOINT { SOLVE dS METHOD cnexp }

DERIVATIVE dS {
  s' = 42*s + 23
}
",
        )
        .unwrap();
        let m = &ast::Module::new(&s)
            .unwrap()
            .solve_odes()
            .unwrap()
            .splat_blocks()
            .unwrap();
        let StatementT::Assign(lhs, rhs) = &m
            .breakpoint
            .as_ref()
            .unwrap()
            .body
            .stmnts
            .last()
            .unwrap()
            .data
        else {
            panic!();
        };
        let rhs = rhs.simplify().unwrap();
        let e = Parser::new_from_str("-ba_ + (s + ba_) * exp(23 * dt)")
            .expression()
            .unwrap()
            .simplify()
            .unwrap();
        assert_eq!(lhs, "s");
        assert!(e.equivalent(&rhs));
    }
}
