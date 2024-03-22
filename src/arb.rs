use crate::{
    ast::{Module, KNOWN},
    err::ModcxxError,
    err::Result,
    exp::{Callable, Expression, Operator, Statement, Symbol, Unit},
    loc::Location,
    usr::Uses,
    Set,
};

pub fn arborize(module: &Module) -> Result<Module> {
    let mut module = module.clone();

    // Sanitize module
    globals_to_arguments(&mut module);
    clean_up_assigned(&mut module);
    merge_non_specifics(&mut module);

    // NET_RECEIVE in NEURON takes a vector of args of which the _first_ is
    // 'weight' and the rest is more like a PARAMETER _per_ connection. Arbor
    // doesn't allow that, so barf up an error.
    if let Some(proc) = &mut module.net_receive {
        if let Some(args) = &proc.args {
            if args.len() > 1 {
                return Err(ModcxxError::ArborUnsupported(
                    "Per connection parameters in NET_RECEIVE.".to_string(),
                ));
            }
        }
    }

    // NEURON allows _writing_ to PARAMETER with dubious implications.
    for proc in module
        .procedures
        .iter_mut()
        .chain(module.kinetics.iter_mut())
        .chain(
            [
                &mut module.initial,
                &mut module.breakpoint,
                &mut module.net_receive,
            ]
            .iter_mut()
            .filter_map(|b| b.as_mut()),
        )
    {
        let writes = proc
            .uses()
            .iter()
            .filter_map(|(k, v)| {
                if !v.writes.is_empty() {
                    Some(k.to_string())
                } else {
                    None
                }
            })
            .collect::<Set<_>>();
        for param in &module.parameters {
            if KNOWN.iter().any(|s| s.0 == param.name) {
                continue;
            }
            if writes.contains(&param.name) {
                return Err(ModcxxError::ArborUnsupported(format!(
                    "PARAMETER {} is written",
                    param.name
                )));
            }
        }
    }

    // NEURON doesn't say what to do with PARAMETER, we default to RANGE
    for param in &module.parameters {
        if !module.ranges.contains(&param.name)
            && !module.globals.contains(&param.name)
            && !KNOWN.iter().any(|v| *v.0 == param.name)
        {
            module.ranges.push(param.name.to_string());
        }
    }

    for ass in &module.assigned {
        if !module.ranges.contains(&ass.name) {
            module.ranges.push(ass.name.to_string());
        }
    }

    // FUNCTION may never write anything globally visible
    for func in module.functions.iter() {
        if let Some((k, e)) = func.uses().iter().find(|kv| !kv.1.writes.is_empty()) {
            return Err(ModcxxError::NonPureFunction(
                func.name.to_string(),
                k.to_string(),
                e.writes.first().unwrap().src,
            ));
        }
    }

    // Clean-up any mess we made above.
    module = module.eliminate_dead_globals()?;

    Ok(module)
}

/// Scan all procedures and functions:
///
/// If they utilize a global variable, we need to add it to the argument list.
fn globals_to_arguments(module: &mut Module) {
    let mut globals = vec![Symbol::argument(
        "v",
        Some(Unit::variable("mV", Location::default())),
        Location::default(),
    )];
    for ion in &module.ions {
        for var in &ion.vars {
            globals.push(Symbol::argument(
                &var.name,
                var.unit.clone(),
                Location::default(),
            ));
        }
    }

    fn extend_dummies(proc: &mut Callable, globals: &[Symbol]) {
        // `uses` suppresses shadowed variables.
        let variables = proc.uses().0;
        if let Some(ref mut args) = &mut proc.args {
            for global in globals {
                if variables.contains_key(&global.name)
                    && !args.iter().any(|s| s.name == global.name)
                {
                    args.push(global.clone());
                }
            }
        }
    }

    module
        .procedures
        .iter_mut()
        .for_each(|p| extend_dummies(p, &globals));
    module
        .functions
        .iter_mut()
        .for_each(|p| extend_dummies(p, &globals));
}

/// Remove dubious ASSIGNED and PARAMETER
///
/// - Dump all ionic variables from PARAMETER, ASSIGNED, and RANGE
/// - Remove voltage from ASSIGNED and RANGE
fn clean_up_assigned(module: &mut Module) {
    let known = KNOWN
        .iter()
        .map(|(v, u)| {
            Symbol::parameter(
                v,
                Some(Unit::variable(u, Location::default())),
                None,
                None,
                Location::default(),
            )
        })
        .collect::<Vec<_>>();

    let mut blacklist = known.clone();
    for ion in &module.ions {
        for var in &ion.vars {
            blacklist.push(var.clone());
        }
    }
    for var in &module.non_specific_currents {
        blacklist.push(var.clone());
    }

    module
        .parameters
        .retain(|s| !blacklist.iter().any(|v| v.name == s.name));
    module
        .assigned
        .retain(|s| !blacklist.iter().any(|v| v.name == s.name));
    module
        .ranges
        .retain(|s| !blacklist.iter().any(|v| v.name == *s));

    // Now feed back the original list to PARAMETER for later use
    for var in known.into_iter() {
        module.parameters.push(var);
    }
}

/// NEURON allows multiple NONSPECIFIC_CURRENTS; Arbor not.
///
/// Fix by adding all these together.
fn merge_non_specifics(module: &mut Module) {
    let name = "i_total";
    let nsc = &module.non_specific_currents;
    if nsc.len() <= 1 {
        return;
    }

    let mut exp = Expression::variable(&nsc.first().unwrap().name, Location::default());
    for curr in &module.non_specific_currents[1..] {
        let rhs = Expression::variable(&curr.name, Location::default());
        exp = Expression::binary(exp, Operator::Add, rhs, Location::default());
    }
    let stmnt = Statement::assign(name, exp, Location::default());

    if let Some(ref mut bp) = module.breakpoint {
        bp.body.stmnts.push(stmnt);
    }
    module.non_specific_currents = vec![Symbol::global(name, Location::default())];
}
