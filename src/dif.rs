use crate::{
    err::{ModcxxError::InternalError, Result},
    exp::{Expression, ExpressionT, Operator},
    opt::Simplify,
};

pub type Env = Vec<Vec<(String, ExpressionT)>>;

pub fn derivative(exp: &Expression, var: &str) -> Result<Expression> {
    let exp = exp.simplify()?;
    let loc = exp.loc;
    match &exp.data {
        ExpressionT::Unary(op, rhs) => {
            let rhs = derivative(rhs, var)?.simplify()?;
            Ok(Expression::unary(*op, rhs, loc))
        }
        ExpressionT::Binary(ls, op, rs) => match op {
            Operator::Add | Operator::Sub => Expression::binary(
                derivative(ls, var)?.simplify()?,
                *op,
                derivative(rs, var)?.simplify()?,
                loc,
            )
            .simplify(),
            Operator::Mul => {
                let dl = derivative(ls, var)?.simplify()?;
                let dr = derivative(rs, var)?.simplify()?;
                Expression::add(
                    Expression::mul(dl, *rs.clone(), loc),
                    Expression::mul(*ls.clone(), dr, loc),
                    loc,
                )
                .simplify()
            }
            Operator::Div => {
                let dl = derivative(ls, var)?.simplify()?;
                let dr = derivative(rs, var)?.simplify()?;
                Expression::div(
                    Expression::sub(
                        Expression::mul(dl, *rs.clone(), loc),
                        Expression::mul(*ls.clone(), dr, loc),
                        loc,
                    ),
                    Expression::mul(*rs.clone(), *rs.clone(), loc),
                    loc,
                )
                .simplify()
            }
            Operator::Pow => {
                let dl = derivative(ls, var)?.simplify()?;
                let dr = derivative(rs, var)?.simplify()?;
                Expression::mul(
                    exp.clone(),
                    Expression::add(
                        Expression::div(Expression::mul(dl, *rs.clone(), loc), *ls.clone(), loc),
                        Expression::mul(dr, Expression::call("ln", vec![*ls.clone()], loc), loc),
                        loc,
                    ),
                    loc,
                )
                .simplify()
            }
            _ => Err(InternalError(format!(
                "Requested derivative of x {op} y, which doesn't exist."
            ))),
        },
        ExpressionT::Variable(v) => Ok(Expression::float((var == v) as u64, loc)),
        ExpressionT::Number(_) => Ok(Expression::float(0, loc)),
        ExpressionT::String(_) => Err(InternalError(format!(
            "Requested derivative of a string, which doesn't exist."
        ))),
        ExpressionT::Call(_, _) => Err(InternalError(format!(
            "Requested derivative of a call, which isn't implemented."
        ))),
    }
}
