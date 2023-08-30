use crate::{
    ast::Module,
    err::{ModcxxError, Result},
    exp::{
        Access, Block, Callable, Expression, ExpressionT, Operator, Solver, Statement, StatementT,
        Symbol, Unit, Variable,
    },
    par::Kind,
};

pub fn to_nmodl(module: &Module) -> Result<String> {
    let mut res: Vec<String> = Vec::new();

    if let Some(t) = &module.title {
        res.push(format!("TITLE {}", t.trim()));
    }

    if let Some(d) = &module.description {
        let mut tmp = Vec::new();
        tmp.push("COMMENT".to_string());
        for l in d.split('\n') {
            let l = l.trim();
            if l.is_empty() {
                continue;
            }
            tmp.push(format!("  {}", l));
        }
        tmp.push("ENDCOMMENT".to_string());
        res.push(tmp.join("\n"));
    }

    res.push(neuron(module)?);

    if !module.units.is_empty() {
        res.push(units(&module.units)?);
    }

    if !module.constants.is_empty() {
        res.push(constants(&module.constants)?);
    }

    if !module.parameters.is_empty() {
        res.push(parameters(&module.parameters)?);
    }

    if !module.assigned.is_empty() {
        res.push(assigned(&module.assigned)?);
    }

    if !module.states.is_empty() {
        res.push(state(&module.states)?);
    }

    if let Some(init) = &module.initial {
        res.push(initial(init)?);
    }

    if let Some(bp) = &module.breakpoint {
        res.push(breakpoint(bp)?);
    }

    for proc in &module.derivatives {
        res.push(derivative(proc)?);
    }

    for proc in &module.kinetics {
        res.push(kinetic(proc)?);
    }

    if let Some(proc) = &module.net_receive {
        res.push(net_receive(proc)?);
    }

    for proc in &module.procedures {
        res.push(procedure(proc)?);
    }

    for proc in &module.functions {
        res.push(function(proc)?);
    }

    Ok(res.join("\n\n"))
}

fn neuron(nrn: &Module) -> Result<String> {
    let mut res: Vec<String> = Vec::new();
    res.push("NEURON {".into());
    let tag = match nrn.kind {
        Kind::Density => "SUFFIX",
        Kind::Point => "POINT_PROCESS",
        Kind::ArtificialCell => {
            return Err(ModcxxError::ArborUnsupported("Artificial Cells".into()))
        }
    };
    // assert name is not empty
    res.push(format!("  {tag} {}", nrn.name));
    if !nrn.globals.is_empty() {
        res.push(format!("  GLOBAL {}", nrn.globals.join(", ")));
    }
    if !nrn.ranges.is_empty() {
        res.push(format!("  RANGE {}", nrn.ranges.join(", ")));
    }
    for ion in &nrn.ions {
        let mut row = format!("  USEION {}", ion.name);
        let mut rds = Vec::new();
        let mut wrs = Vec::new();
        for var in &ion.vars {
            match var.access {
                Access::RO => rds.push(var.name.to_string()),
                Access::RW => wrs.push(var.name.to_string()),
            }
        }
        if !rds.is_empty() {
            row.push_str(&format!(" READ {}", rds.join(", ")));
        }
        if !wrs.is_empty() {
            row.push_str(&format!(" WRITE {}", wrs.join(", ")));
        }
        res.push(row);
    }
    if !&nrn.non_specific_currents.is_empty() {
        res.push(format!(
            "  NONSPECIFIC_CURRENT {}",
            &nrn.non_specific_currents
                .iter()
                .map(|s| s.name.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    res.push("}".into());
    Ok(res.join("\n"))
}

fn units(raw: &[(Unit, Unit)]) -> Result<String> {
    let mut len = 0;
    let mut names = Vec::new();
    for (nm, desc) in raw {
        match &nm.data {
            ExpressionT::Variable(nm) => {
                names.push((nm.to_string(), unit(&desc.data)?));
                len = std::cmp::max(len, nm.len());
            }
            ExpressionT::Binary(lhs, Operator::Sub, rhs) => {
                let nm = format!("{}-{}", unit(&lhs.data)?, unit(&rhs.data)?);
                len = std::cmp::max(len, nm.len());
                names.push((nm, unit(&desc.data)?));
            }
            _ => {
                println!("{:?}", nm);
                unreachable!()
            }
        }
    }

    let mut res: Vec<String> = Vec::new();
    res.push("UNITS {".into());
    for (k, v) in names {
        let ind = len - k.len();
        res.push(format!("  ({k}){:ind$} = ({v})", ""));
    }
    res.push("}".into());

    Ok(res.join("\n"))
}

fn unit(ex: &ExpressionT) -> Result<String> {
    let mut res = String::new();
    fn unit_(ex: &ExpressionT, res: &mut String) -> Result<()> {
        match ex {
            ExpressionT::Variable(var) => {
                res.push_str(var);
            }
            ExpressionT::Number(var) => {
                res.push_str(var);
            }
            ExpressionT::Binary(lhs, op, rhs) => {
                unit_(&lhs.data, res)?;
                res.push_str(&format!("{op}"));
                unit_(&rhs.data, res)?;
            }
            ExpressionT::Unary(op, rhs) => {
                res.push_str(&format!("{op}"));
                unit_(&rhs.data, res)?;
            }
            u => panic!("Unhandled unit: {:?}", u),
        }
        Ok(())
    }
    unit_(ex, &mut res)?;
    Ok(res)
}

fn parameters(params: &[Symbol]) -> Result<String> {
    let mut res = Vec::new();
    for param in params.iter() {
        res.push(format!("  {}", param.name));
    }

    let len = res.iter().fold(0, |a, s| std::cmp::max(a, s.len()));

    for (param, ref mut rs) in params.iter().zip(res.iter_mut()) {
        if let Some(val) = &param.start {
            let len = len - rs.len();
            rs.push_str(&format!("{:len$} = {val}", "",));
        }
    }

    let len = res.iter().fold(0, |a, s| std::cmp::max(a, s.len()));

    for (param, ref mut rs) in params.iter().zip(res.iter_mut()) {
        if let Some(ex) = &param.unit {
            let len = len - rs.len();
            rs.push_str(&format!("{:len$} ({})", "", unit(&ex.data)?));
        }
    }

    res.insert(0, String::from("PARAMETER {"));
    res.push("}".into());

    Ok(res.join("\n"))
}

fn assigned(assign: &[Symbol]) -> Result<String> {
    let mut res = Vec::new();
    for var in assign.iter() {
        res.push(format!("  {}", var.name));
    }

    let len = res.iter().fold(0, |a, s| std::cmp::max(a, s.len()));

    for (var, ref mut rs) in assign.iter().zip(res.iter_mut()) {
        if let Some(val) = &var.start {
            let len = len - rs.len();
            rs.push_str(&format!("{:len$} = {val}", "",));
        }
    }

    let len = res.iter().fold(0, |a, s| std::cmp::max(a, s.len()));

    for (var, ref mut rs) in assign.iter().zip(res.iter_mut()) {
        if let Some(ex) = &var.unit {
            let len = len - rs.len();
            rs.push_str(&format!("{:len$} ({})", "", unit(&ex.data)?));
        }
    }

    res.insert(0, String::from("ASSIGNED {"));
    res.push("}".into());

    Ok(res.join("\n"))
}

fn expression(ex: &Expression) -> Result<String> {
    expression_with_precedence(ex, Operator::Nil)
}

fn expression_with_precedence(ex: &Expression, out: Operator) -> Result<String> {
    let res = match &ex.data {
        ExpressionT::Variable(v) => v.to_string(),
        ExpressionT::Binary(l, o, r) if *o < out => format!(
            "({} {o} {})",
            expression_with_precedence(l, *o)?,
            expression_with_precedence(r, *o)?
        ),
        ExpressionT::Binary(l, o, r) => format!(
            "{} {o} {}",
            expression_with_precedence(l, *o)?,
            expression_with_precedence(r, *o)?
        ),
        ExpressionT::Unary(o, r) => format!("{o}{}", expression_with_precedence(r, *o)?), // PRECEDENCE!!!
        ExpressionT::Call(fun, args) => format!(
            "{fun}({})",
            args.iter()
                .map(expression)
                .collect::<Result<Vec<_>>>()?
                .join(", ")
        ),
        ExpressionT::Number(v) => v.to_string(),
        ExpressionT::String(v) => format!(r#""{v}""#),
    };
    Ok(res)
}

fn statement(stmnt: &Statement, ind: usize, func: Option<&str>) -> Result<String> {
    let mut res = Vec::new();
    match &stmnt.data {
        StatementT::Assign(lhs, rhs) => {
            res.push(format!("{:ind$}{lhs} = {}", "", expression(rhs)?))
        }
        StatementT::Return(rhs) => {
            if let Some(f) = func {
                res.push(format!("{:ind$}{f} = {}", "", expression(rhs)?))
            } else {
                return Err(ModcxxError::InternalError(
                    "Can only return from function.".into(),
                ));
            }
        }
        StatementT::Call(call) => res.push(format!("{:ind$}{}", "", expression(call)?)),
        StatementT::Block(blk) => {
            res.push(format!("{:ind$}{{", ""));
            let ind = ind + 2;
            if !blk.locals.is_empty() {
                res.push(format!(
                    "{:ind$}LOCAL {}",
                    "",
                    blk.locals
                        .iter()
                        .map(|s| s.name.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                ));
                res.push(String::new());
            }
            for stmnt in &blk.stmnts {
                res.push(statement(stmnt, ind, func)?);
            }
            let ind = ind - 2;
            res.push(format!("{:ind$}}}", ""));
        }
        StatementT::Derivative(nm, ex) => {
            res.push(format!("{:ind$}{nm}' = {}", "", expression(ex)?))
        }
        StatementT::Rate(l, r, f, b) => res.push(format!(
            "{:ind$} ~ {} <-> {} ({}, {})",
            "",
            l,
            r,
            expression(f)?,
            expression(b)?
        )),
        StatementT::IfThenElse(c, ts, es) => {
            res.push(format!(
                "{:ind$}if ({}) {}",
                "",
                expression(c)?,
                statement(ts, ind, func)?.trim_start()
            ));
            if let Some(es) = es {
                res.push(format!(
                    "{:ind$}else {}",
                    "",
                    statement(es, ind, func)?.trim_start()
                ));
            }
        }
        StatementT::Solve(d, m) => {
            let ln = match m {
                Solver::Default => format!("{:ind$}SOLVE {}", "", d),
                Solver::Method(m) => format!("{:ind$}SOLVE {} METHOD {}", "", d, m),
                Solver::SteadyState(m) => format!("{:ind$}SOLVE {} STEADYSTATE {}", "", d, m),
            };
            res.push(ln);
            res.push(String::new());
        }
        StatementT::Conserve(l, r) => {
            res.push(format!(
                "{:ind$}CONSERVE {} = {}",
                "",
                expression(l)?,
                expression(r)?
            ));
        }
        StatementT::Initial(_) => unreachable!(), // This must be removed/rewritten before!
    }
    Ok(res.join("\n"))
}

fn initial(proc: &Callable) -> Result<String> {
    Ok(format!("INITIAL {}", block(&proc.body, 0, None)?))
}

fn state(states: &[Variable]) -> Result<String> {
    let mut res = Vec::new();
    for state in states {
        res.push(format!("  {}", state.name));
    }

    let len = res.iter().fold(0, |a, s| std::cmp::max(a, s.len()));

    for (state, ref mut row) in states.iter().zip(res.iter_mut()) {
        if let Some(val) = &state.start {
            let len = len - row.len();
            row.push_str(&format!("{:len$} = {val}", "",));
        }
    }

    let len = res.iter().fold(0, |a, s| std::cmp::max(a, s.len()));

    for (state, ref mut row) in states.iter().zip(res.iter_mut()) {
        if let Some(ex) = &state.unit {
            let len = len - row.len();
            row.push_str(&format!("{:len$} ({})", "", unit(&ex.data)?));
        }
    }

    res.insert(0, String::from("STATE {"));
    res.push("}".into());

    Ok(res.join("\n"))
}

fn procedure(proc: &Callable) -> Result<String> {
    Ok(format!(
        "PROCEDURE {}({}) {}",
        proc.name,
        proc.args
            .as_deref()
            .unwrap_or_default()
            .iter()
            .map(|arg| arg.name.to_string())
            .collect::<Vec<_>>()
            .join(", "),
        block(&proc.body, 0, None)?
    ))
}

fn net_receive(proc: &Callable) -> Result<String> {
    Ok(format!(
        "NET_RECEIVE ({}) {}",
        proc.args
            .as_deref()
            .unwrap_or_default()
            .iter()
            .map(|s| s.name.to_string())
            .collect::<Vec<_>>()
            .join(", "),
        block(&proc.body, 0, None)?
    ))
}

fn function(proc: &Callable) -> Result<String> {
    Ok(format!(
        "FUNCTION {}({}) {}",
        proc.name,
        proc.args
            .as_deref()
            .unwrap_or_default()
            .iter()
            .map(|s| s.name.to_string())
            .collect::<Vec<_>>()
            .join(", "),
        block(&proc.body, 0, Some(&proc.name))?
    ))
}

fn block(block: &Block, ind: usize, func: Option<&str>) -> Result<String> {
    let mut res = Vec::new();
    res.push(format!("{:ind$}{{", ""));
    if !block.locals.is_empty() {
        res.push(format!(
            "  LOCAL {}",
            block
                .locals
                .iter()
                .map(|s| s.name.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        ));
        res.push(String::new());
    }
    for stmnt in &block.stmnts {
        res.push(statement(stmnt, ind + 2, func)?);
    }
    res.push(format!("{:ind$}}}", ""));
    Ok(res.join("\n"))
}

fn breakpoint(proc: &Callable) -> Result<String> {
    Ok(format!("BREAKPOINT {}", block(&proc.body, 0, None)?))
}

fn derivative(proc: &Callable) -> Result<String> {
    Ok(format!(
        "DERIVATIVE {} {}",
        proc.name,
        block(&proc.body, 0, None)?
    ))
}

fn kinetic(proc: &Callable) -> Result<String> {
    Ok(format!(
        "KINETIC {} {}",
        proc.name,
        block(&proc.body, 0, None)?
    ))
}

fn constants(symbols: &[Variable]) -> Result<String> {
    let mut res = Vec::new();
    for symbol in symbols {
        res.push(format!("  {}", symbol.name));
    }

    let len = res.iter().fold(0, |a, s| std::cmp::max(a, s.len()));

    for (symbol, ref mut rs) in symbols.iter().zip(res.iter_mut()) {
        let val = if let Some(val) = &symbol.start {
            val
        } else {
            match symbol.name.as_ref() {
                "FARADAY" => "96485.3321",
                "R" => "8.31446261815324",
                "PI" => "3.14159265359",
                _ => todo!(),
            }
        };
        let len = len - rs.len();
        rs.push_str(&format!("{:len$} = {val}", "",));
    }

    let len = res.iter().fold(0, |a, s| std::cmp::max(a, s.len()));

    for (symbol, ref mut rs) in symbols.iter().zip(res.iter_mut()) {
        if let Some(ex) = &symbol.unit {
            let len = len - rs.len();
            rs.push_str(&format!("{:len$} ({})", "", unit(&ex.data)?));
        }
    }

    res.insert(0, String::from("CONSTANT {"));
    res.push("}".into());

    Ok(res.join("\n"))
}
