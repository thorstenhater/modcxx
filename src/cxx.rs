use crate::{
    ast::{Module, KNOWN}, err::Result, exp::{
        Callable, Expression, ExpressionT, Operator, Statement, StatementT,
    }, usr::{Inventory, Uses}, Map, Set
};

#[derive(Debug, Default, Clone)]
struct CxxCtx {
    ind: usize,
    builtin_vectors: Vec<String>,
    builtin_scalars: Vec<String>,
    symbols: Map<String, usize>,
    params: Map<String, usize>,
    globals: Map<String, usize>,
    states: Map<String, usize>,
    ionics: Map<String, (usize, String)>,
}

impl CxxCtx {
    fn read_var(&self, n: &String) -> String {
        if let Some(i) = self.symbols.get(n) {
            format!("{n}_{i}")
        } else {
            format!("{n}")
        }
    }
}

fn stmnt_cxx_def(stmnt: &Statement, ctx: &mut CxxCtx) -> String {
    match &stmnt.data {
        StatementT::Assign(n, rhs) => {
            let rhs = exp_cxx_def(&rhs, ctx);
            let v = ctx.symbols.entry(n.to_string()).or_insert(0);
            *v += 1;
            let i = *v;
            format!("{:ind$}auto {n}_{i} = {rhs};", "", ind = ctx.ind)
        }
        StatementT::Return(ex) => format!("{:ind$}return {};", "", exp_cxx_def(ex, ctx), ind = ctx.ind),
        StatementT::Conserve(_, _) => format!("{:ind$}//TODO conserve", "", ind = ctx.ind),
        StatementT::Rate(_, _, _, _) => format!("{:ind$}//TODO rate", "", ind = ctx.ind),
        StatementT::Derivative(_, _) => format!("{:ind$}//TODO diff", "", ind = ctx.ind),
        StatementT::IfThenElse(_, _, _) => {
            format!("{:ind$} //TODO ifthenelse", "", ind = ctx.ind)
        }
        StatementT::Block(_) => format!("{:ind$}//TODO block", "", ind = ctx.ind),
        StatementT::Call(_, _) => format!("{:ind$}//TODO call", "", ind = ctx.ind),
        StatementT::Initial(_) => format!("{:ind$}//TODO init", "", ind = ctx.ind),
        StatementT::Linear(_, _) => format!("{:ind$}//TODO linear", "", ind = ctx.ind),
        StatementT::Solve(_, _) => format!("{:ind$}//TODO solve", "", ind = ctx.ind),
        StatementT::For(_, _, _, _) => format!("{:ind$}//TODO for", "", ind = ctx.ind),
        StatementT::While(_, _) => format!("{:ind$}//TODO while", "", ind = ctx.ind),
    }
}

fn op_cxx_def(op: &Operator) -> String {
    format!("{op}")
}

fn exp_cxx_def(exp: &Expression, ctx: &CxxCtx, ) -> String {
    match &exp.data {
        crate::exp::ExpressionT::Unary(op, ex) => format!("{}{}", op_cxx_def(op), exp_cxx_def(ex, ctx),),
        crate::exp::ExpressionT::Binary(Operator::Pow, l, r) => {
            format!("pow({}, {})", exp_cxx_def(l, ctx), exp_cxx_def(r, ctx))
        }
        crate::exp::ExpressionT::Binary(o, l, r) => {
            let l = match l.data {
                ExpressionT::Binary(ol, _, _) if ol < *o => format!("({})", exp_cxx_def(l, ctx)),
                _ => exp_cxx_def(l, ctx),
            };
            let r = match r.data {
                ExpressionT::Binary(or, _, _) if or < *o => format!("({})", exp_cxx_def(r, ctx)),
                _ => exp_cxx_def(r, ctx),
            };
            format!("{} {} {}", l, op_cxx_def(o), r)
        }
        crate::exp::ExpressionT::Variable(n) => {
            ctx.read_var(n)
        }
        crate::exp::ExpressionT::Number(n) => {
            format!("{}", n.to_f64())
        }
        crate::exp::ExpressionT::String(n) => format!("\"{n}\""),
        crate::exp::ExpressionT::Call(fun, args) => format!(
            "{}({})",
            fun,
            args.iter().map(|arg| exp_cxx_def(arg, ctx)).collect::<Vec<_>>().join(", "),
        ),
    }
}

fn fun_cxx_def(fun: &Callable, ctx: &mut CxxCtx) -> String {
    let mut ctx = ctx.clone();
    let mut res = Vec::new();
    res.push(format!("{} {{", fun_cxx_decl(fun, false, &mut ctx)));
    ctx.ind += 4;

    let blk = &fun.body;
    let uses = blk.uses();

    let globals = ctx
        .globals
        .iter()
        .filter(|p| uses.is_read(p.0).is_some())
        .collect::<Vec<_>>();
    if !globals.is_empty() {
        res.push(format!("{:ind$}// GLOBAL", "", ind = ctx.ind));
        for (var, idx) in &globals {
            res.push(format!(
                "{:ind$}double {var} = ppack->globals[{idx}];",
                "",
                ind = ctx.ind
            ));
        }
    }

    res.push(format!("{:ind$}// BODY", "", ind = ctx.ind));
    for stmnt in &blk.stmnts {
        res.push(stmnt_cxx_def(stmnt, &mut ctx));
    }

    ctx.ind -= 4;
    res.push(format!("{:ind$}}}", "", ind = ctx.ind));
    res.join("\n")
}

fn read_ppack_vector(ps: &Map<String, usize>, arr: &str, uses: &Inventory, ctx: &CxxCtx, res: &mut Vec<String>) {
    let ps = ps.iter()
                .filter(|p| !ctx.builtin_scalars.contains(p.0))
                .filter(|p| !ctx.builtin_vectors.contains(p.0))
                .filter(|p| uses.is_read(p.0).is_some())
                .collect::<Vec<_>>();
    if !ps.is_empty() {
        res.push(format!("{:ind$}// {arr}", "", ind = ctx.ind));
        for (var, idx) in &ps {
            res.push(format!(
                "{:ind$}double {var} = ppack->{arr}[{idx}];",
                "",
                ind = ctx.ind
            ));
        }
    }
}

fn api_cxx_def(fun: &Callable, ctx: &mut CxxCtx) -> String {
    let mut ctx = ctx.clone();
    let blk = &fun.body;
    let uses = blk.uses();
    let mut in_scope = Vec::new();

    let mut res = Vec::new();
    res.push(format!("{} {{", fun_cxx_decl(fun, true, &mut ctx)));
    ctx.ind += 4;

    let globals = ctx
        .globals
        .iter()
        .filter(|p| uses.is_read(p.0).is_some())
        .collect::<Vec<_>>();
    if !globals.is_empty() {
        res.push(format!("{:ind$}// GLOBAL", "", ind = ctx.ind));
        for (var, idx) in &globals {
            res.push(format!(
                "{:ind$}double {var} = ppack->globals[{idx}];",
                "",
                ind = ctx.ind
            ));
            in_scope.push(var.to_string());
        }
    }

    res.push(format!(
        "{:ind$}for (auto cv = 0ul; cv < ppack->width; ++cv) {{",
        "",
        ind = ctx.ind
    ));
    ctx.ind += 4;
    res.push(format!(
        "{:ind$}auto cv_idx = ppack->node_index[cv];",
        "",
        ind = ctx.ind
    ));
    read_ppack_vector(&ctx.params, "parameters", &uses, &ctx, &mut res);

    let ionics = ctx
        .ionics
        .iter()
        .filter(|p| uses.is_read(p.0).is_some())
        .map(|(v, (i, s))| (v.clone(), (*i, s.clone())))
        .collect::<Vec<(String, (usize, String))>>();
    let mut seen_ions = Set::new();
    if !ionics.is_empty() {
        res.push(format!("{:ind$}// IONICS", "", ind = ctx.ind));
        for (var, (idx, field)) in &ionics {
            if !seen_ions.contains(idx) {
                res.push(format!(
                    "{:ind$}auto ion_{idx}_idx = ppack->ion_states[{idx}].index[cv];",
                    "",
                    ind = ctx.ind
                ));
                seen_ions.insert(idx);
            }
            res.push(format!(
                "{:ind$}auto {var} = ppack->ion_states[{idx}].{field}[ion_{idx}_idx];",
                "",
                ind = ctx.ind
            ));
        }
    }

    read_ppack_vector(&ctx.states, "state_vars", &uses, &ctx, &mut res);

    res.push(format!("{:ind$}// BODY", "", ind = ctx.ind));
    for stmnt in &blk.stmnts {
        res.push(stmnt_cxx_def(stmnt, &mut ctx));
    }

    let ionics = ctx
        .ionics
        .iter()
        .filter(|p| uses.is_written(p.0).is_some())
        .collect::<Vec<_>>();
    if !ionics.is_empty() {
        res.push(format!("{:ind$}// IONICS", "", ind = ctx.ind));
        for (var, (idx, field)) in &ionics {
            if !seen_ions.contains(idx) {
                res.push(format!(
                    "{:ind$}auto ion_{idx}_idx = ppack->ion_states[{idx}].index[cv];",
                    "",
                    ind = ctx.ind
                ));
                seen_ions.insert(idx);
            }
            res.push(format!(
                "{:ind$}ppack->ion_states[{idx}].{field}[ion_{idx}_idx] = {};",
                "",
                ctx.read_var(var),
                ind = ctx.ind
            ));
        }
    }

    let states = ctx
        .states
        .iter()
        .filter(|p| uses.is_written(p.0).is_some())
        .collect::<Vec<_>>();
    if !states.is_empty() {
        res.push(format!("{:ind$}// ASSIGNED & STATE", "", ind = ctx.ind));
        for (var, idx) in &states {
            res.push(format!(
                "{:ind$}ppack->state_vars[{idx}][cv_idx] = {};",
                "",
                ctx.read_var(var),
                ind = ctx.ind
            ));
        }
    }
    ctx.ind -= 4;
    res.push(format!("{:ind$}}}", "", ind = ctx.ind));

    ctx.ind -= 4;
    res.push(format!("{:ind$}}}", "", ind = ctx.ind));
    res.join("\n")
}

fn cxx_type_of(unit: &Option<Expression>) -> String {
    if let Some(_) = unit {
        String::from("double")
    } else {
        String::from("void")
    }
}

fn fun_cxx_decl(fun: &Callable, have_ppack: bool, ctx: &mut CxxCtx) -> String {
    let mut args = Vec::new();
    if have_ppack {
        args.push(String::from("arb_mechanism_ppack* ppack"));
    }
    if let Some(list) = &fun.args {
        args.extend(list.iter().map(|arg| format!("{} {}",  cxx_type_of(&arg.unit), arg.name)));
    }
    format!(
        "{:ind$}{} {}({})",
        "",
        &cxx_type_of(&fun.unit),
        &fun.name,
        args.join(", "),
        ind = ctx.ind
    )
}

fn ion_var_from(ion: &str, var: &str) -> String {
    let name = if let Some(x) = var.strip_prefix(ion) {
        match x {
            "i" => "internal_concentration",
            "o" => "external_concentration",
            _ => panic!("Cannot find ionic variable for {var} on ion {ion}"),
        }
    } else if let Some(x) = var.strip_suffix(ion) {
        match x {
            "i" => "current_density",
            "e" => "reveral_potential",
            _ => panic!("Cannot find ionic variable for {var} on ion {ion}"),
        }
    } else {
        panic!("Cannot find ionic variable for {var} on ion {ion}");
    };
    String::from(name)
}


fn mod_def_cxx(module: &Module, ctx: &mut CxxCtx) -> String {
    ctx.params = module
        .parameters
        .iter()
        .enumerate()
        .map(|(ix, var)| (var.name.to_string(), ix))
        .collect();
    ctx.builtin_vectors = KNOWN.iter().map(|s| s.0.to_string()).collect::<Vec<_>>();
    ctx.builtin_scalars = ["dt"].iter().map(|s| s.to_string()).collect::<Vec<_>>();
    ctx.globals = module
        .globals
        .iter()
        .enumerate()
        .map(|(ix, s)| (s.to_string(), ix))
        .collect();
    ctx.states = module
        .assigned
        .iter()
        .chain(module.states.iter())
        .enumerate()
        .map(|(ix, s)| (s.name.to_string(), ix))
        .collect();
    for (iidx, ion) in module.ions.iter().enumerate() {
        for var in ion.vars.iter() {
            ctx.ionics.insert(
                var.name.to_string(),
                (iidx, ion_var_from(&ion.name, &var.name)),
            );
        }
    }

    let mut res = Vec::new();
    for fun in &module.functions {
        res.push(format!("{};", fun_cxx_decl(fun, false, ctx)));
    }

    for fun in &module.procedures {
        res.push(fun_cxx_decl(fun, true, ctx));
    }

    if let Some(fun) = &module.initial {
        res.push(api_cxx_def(fun, ctx));
    }

    if let Some(fun) = &module.breakpoint {
        res.push(api_cxx_def(fun, ctx));
    }

    for fun in &module.procedures {
        res.push(api_cxx_def(fun, ctx));
    }

    for fun in &module.functions {
        res.push(fun_cxx_def(fun, ctx));
    }

    res.join("\n\n")
}

pub fn to_cxx(module: &Module) -> Result<String> {
    Ok(mod_def_cxx(module, &mut CxxCtx::default()))
}
