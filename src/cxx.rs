use crate::{
    ast::Module,
    err::Result,
    exp::{Block, Callable, Expression, Operator, Statement, Symbol, Unit},
};

trait ToCxxDef {
    fn def(&self, ind: usize) -> String;
}

impl ToCxxDef for Symbol {
    fn def(&self, ind: usize) -> String {
        format!("{:ind$}{}", "", self.name.to_string())
    }
}

impl ToCxxDef for Statement {
    fn def(&self, ind: usize) -> String {
        match &self.data {
            crate::exp::StatementT::Assign(n, e) => format!("{:ind$}{n} = {}", "", e.def(0)),
            crate::exp::StatementT::Return(_) => todo!(),
            crate::exp::StatementT::Conserve(_, _) => todo!(),
            crate::exp::StatementT::Rate(_, _, _, _) => todo!(),
            crate::exp::StatementT::Derivative(_, _) => todo!(),
            crate::exp::StatementT::IfThenElse(_, _, _) => todo!(),
            crate::exp::StatementT::Block(_) => todo!(),
            crate::exp::StatementT::Call(_) => todo!(),
            crate::exp::StatementT::Initial(_) => todo!(),
            crate::exp::StatementT::Linear(_, _) => todo!(),
        }
    }
}

impl ToCxxDef for Operator {
    fn def(&self, ind: usize) -> String {
        format!("{:ind$}{self}", "")
    }
}

impl ToCxxDef for Expression {
    fn def(&self, ind: usize) -> String {
        match &self.data {
            crate::exp::ExpressionT::Unary(o, e) => format!("{:ind$}{}{}", "", o.def(0), e.def(0)),
            crate::exp::ExpressionT::Binary(l, o, r) => {
                format!("{:ind$}{} {} {}", "", l.def(0), o.def(0), r.def(0))
            }
            crate::exp::ExpressionT::Variable(n) => format!("{:ind$}{n}", ""),
            crate::exp::ExpressionT::Number(n) => format!("{:ind$}{n}", ""),
            crate::exp::ExpressionT::String(n) => format!("{:ind$}\"{n}\"", ""),
            crate::exp::ExpressionT::Call(f, a) => format!(
                "{:ind$}{}({})",
                "",
                f,
                a.iter().map(|a| a.def(0)).collect::<Vec<_>>().join(", ")
            ),
        }
    }
}

impl ToCxxDef for Block {
    fn def(&self, ind: usize) -> String {
        let mut res = Vec::new();
        res.push(String::from("{"));
        for local in &self.locals {
            res.push(local.def(ind + 4));
        }
        for stmnt in &self.stmnts {
            res.push(stmnt.def(ind + 4));
        }
        res.push(String::from("}"));
        res.join("\n")
    }
}

impl ToCxxDef for Callable {
    fn def(&self, ind: usize) -> String {
        let args = if let Some(args) = &self.args {
            args.iter()
                .map(|s| s.decl(ind))
                .collect::<Vec<_>>()
                .join(", ")
        } else {
            String::new()
        };

        format!(
            "{:ind$}{} {}({}) {}",
            "",
            &self.unit.decl(ind),
            &self.name,
            args,
            self.body.def(ind)
        )
    }
}

impl ToCxxDef for Module {
    fn def(&self, ind: usize) -> String {
        let mut res = Vec::new();
        for fun in &self.functions {
            res.push(fun.decl(ind));
        }

        for fun in &self.procedures {
            res.push(fun.decl(ind));
        }

        if let Some(fun) = &self.initial {
            res.push(fun.def(ind));
        }

        if let Some(fun) = &self.breakpoint {
            res.push(fun.def(ind));
        }

        for fun in &self.functions {
            res.push(fun.def(ind));
        }

        for fun in &self.procedures {
            res.push(fun.def(ind));
        }

        res.join("\n\n")
    }
}

trait ToCxxDecl {
    fn decl(&self, ind: usize) -> String;
}

impl ToCxxDecl for Unit {
    fn decl(&self, _: usize) -> String {
        String::from("double")
    }
}

impl ToCxxDecl for Option<Unit> {
    fn decl(&self, ind: usize) -> String {
        if let Some(u) = self {
            u.decl(ind)
        } else {
            String::from("void")
        }
    }
}

impl ToCxxDecl for Symbol {
    fn decl(&self, ind: usize) -> String {
        format!("{} {}", self.unit.decl(ind), self.name.to_string())
    }
}

impl ToCxxDecl for Callable {
    fn decl(&self, ind: usize) -> String {
        let args = if let Some(args) = &self.args {
            args.iter()
                .map(|s| s.decl(ind))
                .collect::<Vec<_>>()
                .join(", ")
        } else {
            String::new()
        };

        format!("{} {}({});", "void", &self.name, args)
    }
}

pub fn to_cxx(module: &Module) -> Result<String> {
    Ok(module.def(0))
}
