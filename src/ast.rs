use crate::{
    err::{ModcxxError, Result},
    exp::{
        Access, Block, Callable, Expression, ExpressionT, Operator, SolveT, Statement, StatementT,
        Symbol, Variable,
    },
    lex::KEYWORDS,
    loc::Location,
    ode::cnexp,
    opt::Simplify,
    par::{self, Ion, Kind, Units},
    usr::{self, Inventory, Uses},
    Map, Set,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Opt {
    O1,
    Ofast,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Module {
    pub name: String,
    pub kind: Kind,
    pub non_specific_currents: Vec<Symbol>,
    pub ions: Vec<Ion>,
    pub ranges: Vec<String>,
    pub globals: Vec<String>,
    pub title: Option<String>,
    pub description: Option<String>,
    pub initial: Option<Callable>,
    pub breakpoint: Option<Callable>,
    pub derivatives: Vec<Callable>,
    pub states: Vec<Symbol>,
    pub assigned: Vec<Symbol>,
    pub parameters: Vec<Symbol>,
    pub units: Units,
    pub procedures: Vec<Callable>,
    pub kinetics: Vec<Callable>,
    pub linears: Vec<Callable>,
    pub functions: Vec<Callable>,
    pub constants: Vec<Symbol>,
    pub net_receive: Option<Callable>,
}

pub const FUNCTIONS: &[(&str, usize)] = &[
    ("exp", 1),
    ("sin", 1),
    ("cos", 1),
    ("exprelr", 1),
    ("fabs", 1),
    ("log", 1),
    ("log10", 1),
    ("max", 2),
    ("min", 2),
];
pub const KNOWN: &[(&str, &str)] = &[
    ("celsius", "degC"),
    ("v", "mV"),
    ("area", "um2"),
    ("diam", "um"),
];

impl Module {
    pub fn new(module: &par::Module) -> Result<Self> {
        let title = match &module.title[..] {
            [] => None,
            [t] => Some(t.0.to_string()),
            [(t0, l0), (t1, l1), ..] => {
                return Err(ModcxxError::DuplicateTitle(
                    t1.to_string(),
                    *l1,
                    t0.to_string(),
                    *l0,
                ))
            }
        };

        let description = if !module.description.is_empty() {
            Some(module.description.join("\n"))
        } else {
            None
        };

        let nrn = match &module.neuron[..] {
            [] => return Err(ModcxxError::MissingBlock("NEURON".into())),
            [n] => n,
            [n0, n1, ..] => {
                return Err(ModcxxError::DuplicateBlock(
                    "NEURON".into(),
                    n0.location,
                    n1.location,
                ))
            }
        };

        let (name, kind) = match &nrn.kind[..] {
            [] => return Err(ModcxxError::MissingKind),
            [k] => (k.name.to_string(), k.kind),
            [k0, k1, ..] => {
                return Err(ModcxxError::DuplicateKind(
                    format!("{:?}", k0.kind),
                    k0.meta,
                    format!("{:?}", k1.kind),
                    k1.meta,
                ))
            }
        };

        let non_specific_currents = nrn.non_specific_currents.clone();
        let ions = nrn.ions.clone();

        let builtins = ions
            .iter()
            .flat_map(|i| i.vars.iter())
            .chain(non_specific_currents.iter())
            .map(|v| v.name.to_string())
            .chain(KNOWN.iter().map(|p| p.0.to_string()))
            .collect::<Vec<_>>();

        let mut ranges = nrn.ranges.clone();
        let globals = nrn.globals.clone();

        let states = module.states.clone();
        // STATE and ions are module local anyhow.
        ranges.retain(|r| !states.iter().any(|s| &s.name == r));
        ranges.retain(|r| !builtins.contains(r));

        let initial = match &module.initial[..] {
            [] => {
                if !states.is_empty() {
                    return Err(ModcxxError::MissingBlock("INITIAL".into()));
                }
                None
            }
            [n] => Some(n.clone()),
            [n0, n1, ..] => {
                return Err(ModcxxError::DuplicateBlock(
                    "INITIAL".into(),
                    n0.loc,
                    n1.loc,
                ))
            }
        };

        let breakpoint = match &module.breakpoint[..] {
            [] => return Err(ModcxxError::MissingBlock("BREAKPOINT".into())),
            [n] => Some(n.clone()),
            [n0, n1, ..] => {
                return Err(ModcxxError::DuplicateBlock(
                    "BREAKPOINT".into(),
                    n0.loc,
                    n1.loc,
                ))
            }
        };

        let net_receive = match &module.net_receive[..] {
            [] => None,
            [n] => Some(n.clone()),
            [n0, n1, ..] => {
                return Err(ModcxxError::DuplicateBlock(
                    "NET_RECEIVE".into(),
                    n0.loc,
                    n1.loc,
                ))
            }
        };

        for var in &module.assigned {
            let nm = &var.name;
            if !ranges.contains(nm) && !globals.contains(nm) && !KNOWN.iter().any(|p| p.0 == nm) {
                ranges.push(nm.to_string());
            }
        }

        let derivatives = module.derivatives.clone();

        let assigned = module
            .assigned
            .iter()
            .filter(|v| !builtins.contains(&v.name))
            .cloned()
            .collect::<Vec<_>>();

        let units = module.units.clone();
        let constants = module.constants.clone();
        let functions = module.functions.clone();
        let procedures = module.procedures.clone();
        let parameters = module
            .parameters
            .iter()
            .filter(|v| !builtins.contains(&v.name))
            .cloned()
            .collect::<Vec<_>>();
        let kinetics = module.kinetics.clone();
        let linears = module.linears.clone();

        let res = Module {
            title,
            name,
            kind,
            non_specific_currents,
            ranges,
            globals,
            ions,
            description,
            initial,
            breakpoint,
            derivatives,
            states,
            assigned,
            units,
            constants,
            functions,
            procedures,
            parameters,
            kinetics,
            linears,
            net_receive,
        };

        check_duplicates_and_keywords(&res)?;
        check_scopes(&res)?;

        Ok(res)
    }

    /// An aggressive pass to remove STATE and ASSIGNED that are never read, but
    /// may possibly be written. This will emit warnings if variables of type
    /// STATE / ASSIGNED are
    ///
    /// 1. defined, but never assigned (initialized)
    /// 2. defined and initialized, but not updated in BREAKPOINT
    /// 3. defined, initialized, and updated, but never read again
    ///
    /// If set to aggressive, it will _remove_ items under 3. This behaviour can
    /// interfere with observability, though.
    pub fn eliminate_dead_state(mut self) -> Result<Self> {
        // First, check all STATE is initialized
        let initialized = self
            .initial
            .as_ref()
            .map(|i| i.uses())
            .unwrap_or(Inventory::new());
        for state in &self.states {
            let state = &state.name;
            if initialized.is_written(&state).is_none() {
                eprintln!("Warning: STATE variable {state} is not initialized in INITIAL block.");
            }
        }

        let mut usage = self
            .breakpoint
            .as_ref()
            .map(|i| i.uses())
            .unwrap_or(Inventory::new());
        usage.merge(
            &self
                .net_receive
                .as_ref()
                .map(|i| i.uses())
                .unwrap_or(Inventory::new()),
        );
        for blk in &self.kinetics {
            usage.merge(&blk.uses());
        }
        for blk in &self.derivatives {
            usage.merge(&blk.uses());
        }

        for state in &self.states {
            let state = &state.name;
            if usage.is_written(&state).is_none()
                && usage.is_written(&format!("{state}'")).is_none()
            {
                eprintln!("Warning: STATE variable {state} is never updated in any BREAKPOINT/NET_RECEIVE/KINETIC/DERIVATIVE block.");
            }
        }

        let mut to_remove = Set::new();
        for state in &self.states {
            let state = &state.name;
            if usage.is_read(&state).is_none() && usage.is_read(&format!("{state}'")).is_none() {
                if initialized.is_read(&state).is_none() {
                    to_remove.insert(state.to_string());
                } else {
                    eprintln!("Warning: STATE variable {state} is never consumed in any BREAKPOINT/NET_RECEIVE/KINETIC/DERIVATIVE block; however it is used in INITIAL.");
                }
            }
        }
        // At this point, we know we can strip all uses of `state` in the module.
        fn strip_writes(
            blk: &mut Block,
            to_remove: &Set<String>,
            locals: &mut Vec<String>,
        ) -> Result<()> {
            locals.extend(blk.locals.iter().map(|v| v.name.to_string()));
            let mut new = Vec::new();
            for stmnt in blk.stmnts.iter() {
                match &stmnt.data {
                    StatementT::Assign(lhs, _)
                        if to_remove.contains(lhs) && !locals.contains(&lhs) => {}
                    StatementT::Block(inner) => {
                        let mut inner = inner.clone();
                        strip_writes(&mut inner, to_remove, locals)?;
                        new.push(Statement::block(inner));
                    }
                    StatementT::IfThenElse(c, t, Some(e)) => {
                        let mut t = t.clone();
                        strip_writes(&mut t, to_remove, locals)?;
                        let mut e = e.clone();
                        strip_writes(&mut e, to_remove, locals)?;
                        new.push(Statement::if_then_else(c.clone(), t, Some(e), stmnt.loc));
                    }
                    StatementT::IfThenElse(c, t, None) => {
                        let mut t = t.clone();
                        strip_writes(&mut t, to_remove, locals)?;
                        new.push(Statement::if_then_else(c.clone(), t, None, stmnt.loc));
                    }
                    _ => new.push(stmnt.clone()),
                }
            }
            blk.stmnts = new;
            // strip back locals
            for _ in &blk.locals {
                locals
                    .pop()
                    .expect("Impossible: left with less locals than we started with");
            }
            Ok(())
        }
        // We also know that these can at most be assignments like `state = ...`
        self.states.retain(|v| !to_remove.contains(&v.name));
        for blk in &mut [
            &mut self.initial,
            &mut self.breakpoint,
            &mut self.net_receive,
        ] {
            if let Some(blk) = blk {
                strip_writes(&mut blk.body, &to_remove, &mut Vec::new())?;
            }
        }

        for procs in &mut [
            &mut self.kinetics,
            &mut self.derivatives,
            &mut self.procedures,
            &mut self.functions,
            &mut self.linears,
        ] {
            for proc in procs.iter_mut() {
                strip_writes(&mut proc.body, &to_remove, &mut Vec::new())?;
            }
        }

        Ok(self)
    }

    pub fn eliminate_dead_blocks(mut self) -> Result<Self> {
        // weed out vacuous callables
        let mut void = Set::new();
        for ps in &[
            &self.procedures,
            &self.linears,
            &self.kinetics,
            &self.derivatives,
            &self.functions,
        ] {
            for p in ps.iter() {
                if p.data.body.stmnts.is_empty() {
                    void.insert(p.name.to_string());
                }
            }
        }

        if let Some(p) = self.initial.as_ref() {
            if p.body.data.stmnts.is_empty() {
                self.initial = None;
            }
        }

        if let Some(p) = self.net_receive.as_ref() {
            if p.body.data.stmnts.is_empty() {
                self.net_receive = None;
            }
        }

        // Let's figure out some data flow
        // NET_RECEIVE, INITIAL, and BREAKPOINT are our entry points
        let mut used = Set::new();
        for blk in &[&self.initial, &self.breakpoint, &self.net_receive] {
            if let Some(blk) = blk {
                for (k, v) in blk.uses().into_iter() {
                    if void.contains(&k) {
                        continue;
                    }
                    if !v.calls.is_empty() || !v.solves.is_empty() {
                        used.insert(k);
                    }
                }
            }
        }

        let mut todo = used.iter().cloned().collect::<Vec<_>>();
        while let Some(name) = todo.pop() {
            for kind in &[
                &self.kinetics,
                &self.derivatives,
                &self.procedures,
                &self.functions,
                &self.linears,
            ] {
                if let Some(blk) = kind.iter().find(|p| p.name == name) {
                    for (k, v) in blk.uses().into_iter() {
                        if used.contains(&k) {
                            continue;
                        }
                        if !v.calls.is_empty() || !v.solves.is_empty() {
                            used.insert(k.clone());
                            todo.push(k);
                        }
                    }
                }
            }
        }

        for kind in &mut [
            &mut self.kinetics,
            &mut self.derivatives,
            &mut self.procedures,
            &mut self.functions,
            &mut self.linears,
        ] {
            kind.retain(|blk| used.contains(&blk.name));
        }
        Ok(self)
    }

    pub fn inline_procedures(mut self) -> Result<Self> {
        let mut procs = Map::new();
        for proc in &self.procedures {
            procs.insert(
                proc.name.to_string(),
                (
                    proc.args
                        .as_deref()
                        .unwrap_or_default()
                        .iter()
                        .map(|s| s.name.to_string())
                        .collect::<Vec<_>>(),
                    proc.body.clone(),
                ),
            );
        }

        for blk in &mut [&mut self.derivatives, &mut self.kinetics] {
            for symbol in blk.iter_mut() {
                symbol.body = inline_procedure_into_block(&symbol.body, &procs)?;
            }
        }

        for blk in &mut [&mut self.initial, &mut self.breakpoint] {
            if let Some(ref mut proc) = blk {
                proc.body = inline_procedure_into_block(&mut proc.body, &procs)?;
            }
        }

        // These can now be deleted
        self.procedures.clear();

        Ok(self)
    }

    pub fn inline_functions(mut self) -> Result<Self> {
        let mut procs = Map::new();
        for proc in &self.functions {
            procs.insert(
                proc.name.to_string(),
                (
                    proc.args
                        .as_deref()
                        .unwrap_or_default()
                        .iter()
                        .map(|s| s.name.to_string())
                        .collect::<Vec<_>>(),
                    proc.body.clone(),
                ),
            );
        }

        for blk in &mut [&mut self.derivatives, &mut self.kinetics] {
            for symbol in blk.iter_mut() {
                symbol.body = inline_function_into_block(&symbol.body, &procs)?;
            }
        }

        for blk in [&mut self.initial, &mut self.breakpoint].iter_mut() {
            if let Some(ref mut proc) = blk {
                proc.body = inline_function_into_block(&proc.body, &procs)?;
            }
        }

        // No need for FUNCTIONs any more; built-ins are covered elsewhere
        self.functions.clear();

        Ok(self)
    }

    pub fn solve_odes(mut self) -> Result<Self> {
        if let Some(ref mut proc) = self.breakpoint {
            for stmnt in proc.body.stmnts.iter_mut() {
                if let StatementT::Solve(ds, method) = &stmnt.data {
                    let ds = self
                        .derivatives
                        .iter()
                        .find(|p| &p.name == ds)
                        .ok_or(ModcxxError::UnboundName(ds.to_string(), stmnt.loc))?;
                    let new = match method {
                        SolveT::Default => cnexp(&ds.body)?,
                        SolveT::Method(m) if m == "cnexp" => cnexp(&ds.body)?,
                        SolveT::Method(_) => todo!(),
                        SolveT::SteadyState(_) => todo!(),
                    };
                    *stmnt = Statement::block(new);
                }
            }
        }
        // We solved all of them, right?
        self.derivatives.clear();
        Ok(self)
    }

    pub fn splat_blocks(mut self) -> Result<Self> {
        for blk in &mut [&mut self.derivatives, &mut self.kinetics] {
            for ref mut block in blk.iter_mut() {
                block.body = block.body.splat_blocks()?
            }
        }

        for blk in &mut [&mut self.initial, &mut self.breakpoint] {
            if let Some(ref mut proc) = blk {
                proc.body = proc.body.splat_blocks()?;
            }
        }

        Ok(self)
    }

    pub fn eliminate_dead_globals(mut self) -> Result<Self> {
        loop {
            let mut used = Set::new();

            for blk in &[&self.initial, &self.breakpoint, &self.net_receive] {
                if let Some(blk) = blk {
                    used.append(&mut blk.uses().0.keys().cloned().collect());
                }
            }

            for blks in &[
                &self.kinetics,
                &self.derivatives,
                &self.procedures,
                &self.functions,
            ] {
                for blk in blks.iter() {
                    used.append(&mut blk.uses().0.keys().cloned().collect());
                }
            }

            let old_len = self.assigned.len()
                + self.constants.len()
                + self.parameters.len()
                + self.states.len()
                + self.ions.iter().fold(0, |acc, ion| acc + ion.vars.len())
                + self.ions.len()
                + self.globals.len()
                + self.ranges.len();

            for vars in &mut [&mut self.constants, &mut self.parameters, &mut self.states] {
                vars.retain(|v| used.contains(&v.name));
            }
            self.ions
                .iter_mut()
                .for_each(|ion| ion.vars.retain(|var| used.contains(&var.name)));
            self.ions.retain(|ion| !ion.vars.is_empty());

            self.ranges.retain(|r| {
                self.assigned.iter().any(|v| r == &v.name)
                    || self.parameters.iter().any(|v| r == &v.name)
            });

            let new_len = self.assigned.len()
                + self.constants.len()
                + self.parameters.len()
                + self.states.len()
                + self.ions.iter().fold(0, |acc, ion| acc + ion.vars.len())
                + self.ions.len()
                + self.globals.len()
                + self.ranges.len();

            if old_len == new_len {
                break;
            }
        }
        Ok(self)
    }

    /// Turns ASSIGNED variables into LOCAL. This transformation should be done
    /// after inlining for it is easier to show to be correct then. Here we
    /// assert complete inlining of PROCEDUREs was done. In general, it is
    /// unsafe to transform ASSIGNED (mutable global state) into LOCAL (mutable
    /// local variables) as a situation like this might occur:
    ///
    /// ASSIGNED { x }
    /// INITIAL { x = 0 }           ? initialised here
    /// BREAKPOINT { x = x + 1 }    ? read and write later
    /// NET_RECEIVE { x = x + 1 }   ? and again
    ///
    /// *However* ASSIGNED are commonly used to pass (multiple) return values
    /// from a PROCEDURE to its caller. Thus, the pattern
    ///
    /// ASSIGNED { x y z }
    /// PROCEDURE foo() { x = 1 y = 2 z = 3 }
    /// BREAKPOINT {
    ///   foo()
    ///   x' = x + y + z
    /// }
    ///
    /// could be safely rewritten as
    ///
    /// BREAKPOINT {
    ///   LOCAL x = 1 y = 2 z = 3
    ///   foo()
    ///   x' = x + y + z
    /// }
    ///
    /// In general, ASSIGNED can be made LOCAL iff no write->read crosses block
    /// boundaries. All of this serves to say: We can make a variable LOCAL if
    /// writing to it has no global effect.  ¯\_(ツ)_/¯
    ///
    /// However, for this we need to assign an order to the blocks, and this
    /// seems to be the sensible one:
    /// 1. INITIAL
    /// 2. BREAKPOINT
    ///   a. Anything SOLVEd; ie KINETIC and/or DERIVATIVE.
    ///      We do not assign an order between SOLVEd blocks.
    ///   b. the body
    /// 3. Optionally: NET_RECEIVE
    /// 4. GOTO 2.
    pub fn assigned_to_local(mut self) -> Result<Self> {
        // Emulate cyclical callgraph by one repetition of the loop
        let mut blocks = Vec::new();
        if let Some(ref blk) = self.initial {
            blocks.push(blk.data.clone());
        }
        if let Some(ref blk) = self.breakpoint {
            blocks.push(blk.data.clone());
        }
        if let Some(ref blk) = self.net_receive {
            blocks.push(blk.data.clone());
        }
        if let Some(ref blk) = self.breakpoint {
            blocks.push(blk.data.clone());
        }
        if let Some(ref blk) = self.net_receive {
            blocks.push(blk.data.clone());
        }
        // Inline all procedures and SOLVEd blocks
        // Functions must be pure, so we can just ignore them.
        fn do_inline(blk: &mut Block, inlinable: &Map<String, Block>) -> Result<()> {
            for stmnt in blk.stmnts.iter_mut() {
                match &mut stmnt.data {
                    StatementT::Block(ref mut blk) => do_inline(blk, inlinable)?,
                    StatementT::IfThenElse(_, ref mut t, Some(ref mut e)) => {
                        do_inline(t, inlinable)?;
                        do_inline(e, inlinable)?;
                    }
                    StatementT::IfThenElse(_, ref mut t, None) => {
                        do_inline(t, inlinable)?;
                    }
                    StatementT::Call(nm, _) if inlinable.contains_key(nm) => {
                        *stmnt = Statement::block(inlinable[nm].clone());
                    }
                    StatementT::Solve(nm, _) if inlinable.contains_key(nm) => {
                        *stmnt = Statement::block(inlinable[nm].clone());
                    }

                    _ => {}
                }
            }
            Ok(())
        }

        // Collect all inlinable blocks regardless of provenance and convert
        // potential arguments into locals.
        let mut inlinable = Map::new();
        for prcs in &[
            &self.derivatives,
            &self.kinetics,
            &self.linears,
            &self.procedures,
        ] {
            for prc in prcs.iter() {
                let mut body = prc.body.clone();
                if let Some(ref args) = prc.args {
                    for arg in args.iter() {
                        body.locals.push(arg.clone());
                    }
                }
                inlinable.insert(prc.name.to_string(), body);
            }
        }

        for ref mut block in blocks.iter_mut() {
            do_inline(&mut block.body, &inlinable)?;
        }

        // With everything in a flat list of blocks, we can build the condition
        // Note that we cannot rely on the canoncical usage list due to the issue
        // of conditionals. We also feed in the list of locals due to shadowing

        // One of Read only, Write only, Write _after_ Read, Read after Write,
        // might be undefined if branches break things
        #[derive(Copy, Clone, PartialEq, Eq)]
        enum Action {
            R,
            W,
            WR,
            RW,
            NA,
        }

        fn add(res: &mut Map<String, Action>, var: &str, act: Action) {
            let new = match res.get(var) {
                Some(Action::NA) => Action::NA,
                Some(Action::RW) => Action::RW,
                Some(Action::WR) => Action::WR,
                Some(Action::W) => {
                    // had W ...
                    match act {
                        Action::W => Action::W,   // WW => W
                        Action::R => Action::WR,  // WR => WR
                        Action::RW => Action::WR, // WRW => WR
                        Action::WR => Action::WR, // WWR => WR
                        Action::NA => Action::NA,
                    }
                }
                Some(Action::R) => {
                    match act {
                        Action::R => Action::R,   // RR => R
                        Action::W => Action::RW,  // RW => RW
                        Action::RW => Action::RW, // RRW => RW
                        Action::WR => Action::WR, // RWR => RW
                        Action::NA => Action::NA,
                    }
                }
                None => act,
            };
            res.insert(var.to_string(), new);
        }

        fn list_accesses(blk: &Block, locals: &mut Vec<String>, res: &mut Map<String, Action>) {
            for v in &blk.locals {
                locals.push(v.name.to_string())
            }
            for stmnt in &blk.stmnts {
                match &stmnt.data {
                    StatementT::Block(blk) => list_accesses(blk, locals, res),
                    StatementT::IfThenElse(c, t, Some(e)) => {
                        for var in c.variables() {
                            add(res, &var, Action::R);
                        }
                        let mut lhs = Map::new();
                        list_accesses(t, locals, &mut lhs);
                        let mut rhs = Map::new();
                        list_accesses(e, locals, &mut rhs);
                        // 3-way merge with missing data
                        let keys = lhs.keys().chain(rhs.keys());
                        for key in keys.into_iter() {
                            match (rhs.get(key), lhs.get(key)) {
                                (None, None) => {}
                                (None, Some(a)) => add(res, key, *a),
                                (Some(a), None) => add(res, key, *a),
                                (Some(a), Some(b)) if a == b => add(res, key, *a),
                                (Some(Action::NA), _) => add(res, key, Action::NA),
                                (_, Some(Action::NA)) => add(res, key, Action::NA),
                                (Some(Action::R), Some(Action::RW)) => add(res, key, Action::RW),
                                (Some(Action::RW), Some(Action::R)) => add(res, key, Action::RW),
                                (Some(Action::W), Some(Action::WR)) => add(res, key, Action::WR),
                                (Some(Action::WR), Some(Action::W)) => add(res, key, Action::WR),
                                _ => add(res, key, Action::NA),
                            }
                        }
                    }
                    StatementT::IfThenElse(c, t, None) => {
                        for var in c.variables() {
                            add(res, &var, Action::R);
                        }
                        list_accesses(t, locals, res);
                    }
                    StatementT::Assign(lhs, rhs) => {
                        add(res, lhs, Action::W);
                        for var in rhs.variables() {
                            add(res, &var, Action::R);
                        }
                    }
                    StatementT::Return(_) => unreachable!(), // we don't handle FUNCTION
                    StatementT::Call(_, _) => unreachable!(), // we have already inlined all of these
                    StatementT::Solve(_, _) => unreachable!(), // we have already inlined all of these
                    StatementT::Initial(_) => unreachable!(),  // Not supported
                    StatementT::Conserve(lhs, rhs) => {
                        // NOTE: We have no clue about the order BUT as we only
                        // talking about ASSIGNED here and CONSERVE is a STATE
                        // thing, we should be good.
                        for v in rhs.variables().iter() {
                            add(res, v, Action::NA);
                        }
                        for v in lhs.variables().iter() {
                            add(res, v, Action::NA);
                        }
                    }
                    StatementT::Rate(lhs, rhs, fw, bw) => {
                        // NOTE: We have no clue about the order BUT as we only
                        // talking about ASSIGNED here and CONSERVE is a STATE
                        // thing, we should be good.
                        for v in rhs.variables().iter() {
                            add(res, v, Action::NA);
                        }
                        for v in lhs.variables().iter() {
                            add(res, v, Action::NA);
                        }
                        // We know about these, though.
                        for v in fw.variables().iter() {
                            add(res, v, Action::R);
                        }
                        for v in bw.variables().iter() {
                            add(res, v, Action::R);
                        }
                    }
                    StatementT::Linear(lhs, rhs) => {
                        for v in rhs.variables().iter() {
                            add(res, v, Action::R);
                        }
                        for v in lhs.variables().iter() {
                            add(res, v, Action::W);
                        }
                    }
                    StatementT::Derivative(lhs, rhs) => {
                        add(res, &format!("{lhs}'"), Action::W);
                        for var in rhs.variables() {
                            add(res, &var, Action::R);
                        }
                    }
                }
            }
            for _ in &blk.locals {
                locals.pop();
            }
        }

        let accesses = blocks
            .iter()
            .map(|blk| {
                let mut locals = Vec::new();
                let mut res = Map::new();
                list_accesses(&blk.body, &mut locals, &mut res);
                res
            })
            .collect::<Vec<_>>();

        let localize = self
            .assigned
            .iter()
            .filter_map(|nm| {
                accesses
                    .iter()
                    .all(|tab| {
                        matches!(tab.get(&nm.name), None | Some(Action::WR) | Some(Action::W))
                    })
                    .then_some(nm.name.to_string())
            })
            .collect::<Set<_>>();
        self.assigned.retain(|v| !localize.contains(&v.name));
        for blk in &mut [
            &mut self.initial,
            &mut self.net_receive,
            &mut self.breakpoint,
        ] {
            if let Some(ref mut blk) = blk {
                for local in localize.iter() {
                    blk.data
                        .body
                        .data
                        .locals
                        .push(Variable::local(local, blk.loc));
                }
            }
        }

        for blk in self.derivatives.iter_mut() {
            for local in localize.iter() {
                blk.data
                    .body
                    .data
                    .locals
                    .push(Variable::local(local, blk.loc));
            }
        }

        Ok(self)
    }

    pub fn kinetic_to_sparse(mut self) -> Result<Self> {
        for kin in self.kinetics.into_iter() {
            let der = kinetic_to_sparse(kin)?.simplify()?;
            self.derivatives.push(der);
        }
        self.kinetics = Vec::new();
        Ok(self)
    }

    pub fn alphatize(mut self) -> Result<Self> {
        let mut globals = Map::new();
        for v in self
            .states
            .iter()
            .chain(self.assigned.iter())
            .chain(self.parameters.iter())
            .chain(self.ions.iter().flat_map(|ion| ion.vars.iter()))
        {
            if let Some(loc) = globals.get(&v.name) {
                return Err(ModcxxError::DuplicateSymbol(
                    v.name.to_string(),
                    v.loc,
                    *loc,
                ));
            }
            globals.insert(v.name.to_string(), v.loc);
        }

        fn do_alphatize(blk: &mut Block, names: &Map<String, Location>) -> Result<()> {
            let mut names = names.clone();
            let mut lut = Map::new();
            for v in &blk.data.locals {
                if names.contains_key(&v.name) {
                    lut.insert(
                        v.name.to_string(),
                        format!("{}_{}_{}_", v.name, v.loc.line, v.loc.column),
                    );
                }
                names.insert(v.name.to_string(), v.loc);
            }
            *blk = blk.rename_all(&lut)?;
            Ok(())
        }

        if let Some(ref mut blk) = self.initial {
            do_alphatize(&mut blk.body, &globals)?;
        }

        Ok(self)
    }

    /// After the other passes, we might be left with local variables that are
    /// never used in the corresponing block. Thus, we remove them from the
    /// block nodes.
    pub fn eliminate_dead_locals(mut self) -> Result<Self> {
        // Helper to recurse through nested blocks in the statement list
        // - Block: recurse into the block
        // - IfThenElse: recurse into the then and else blocks
        fn eliminate_locals(blk: &mut Block) -> Result<()> {
            let uses = blk.uses();
            blk.locals.retain(|l| uses.is_read(&l.name).is_some());
            for stmnt in blk.stmnts.iter_mut() {
                match stmnt.data {
                    StatementT::Block(ref mut blk) => eliminate_locals(blk)?,
                    StatementT::IfThenElse(_, ref mut t, ref mut e) => {
                        eliminate_locals(t)?;
                        if let Some(ref mut e) = e {
                            eliminate_locals(e)?;
                        }
                    }
                    _ => {}
                }
            }
            Ok(())
        }
        for prcs in &mut [
            &mut self.derivatives,
            &mut self.kinetics,
            &mut self.procedures,
            &mut self.functions,
            &mut self.linears,
        ] {
            for prc in prcs.iter_mut() {
                eliminate_locals(&mut prc.body)?;
            }
        }
        for blk in &mut [
            &mut self.initial,
            &mut self.breakpoint,
            &mut self.net_receive,
        ] {
            if let Some(ref mut blk) = blk {
                eliminate_locals(&mut blk.body)?;
            }
        }

        Ok(self)
    }

    /// A dead statement is
    /// 1. writing to a variable that is never read
    /// 2. an empty block (although we should have collapsed those already)
    /// 3. a bare call to a function or procedure that has no effect
    pub fn eliminate_dead_calls(mut self) -> Result<Self> {
        fn eliminate_bare_calls(functions: &Set<String>, blk: &Block) -> Result<Block> {
            let mut res = blk.clone();
            res.stmnts.clear();
            for stmnt in blk.stmnts.iter() {
                match &stmnt.data {
                    StatementT::Call(ref nm, _) if functions.contains(nm) => continue,
                    StatementT::Block(blk) => {
                        res.stmnts
                            .push(Statement::block(eliminate_bare_calls(functions, blk)?));
                    }
                    _ => res.stmnts.push(stmnt.clone()),
                }
            }
            Ok(res)
        }

        let functions = self
            .functions
            .iter()
            .map(|f| f.name.to_string())
            .collect::<Set<_>>();

        for blk in &mut [
            &mut self.initial,
            &mut self.breakpoint,
            &mut self.net_receive,
        ] {
            if let Some(ref mut blk) = blk {
                blk.body = eliminate_bare_calls(&functions, &blk.body)?;
            }
        }

        for prcs in &mut [
            &mut self.derivatives,
            &mut self.kinetics,
            &mut self.procedures,
            &mut self.functions,
            &mut self.linears,
        ] {
            for prc in prcs.iter_mut() {
                prc.body = eliminate_bare_calls(&functions, &prc.body)?;
            }
        }

        Ok(self)
    }

    /// This is a global pass as we need to ensure that _outputs_ are properly
    /// preserved.
    pub fn eliminate_dead_local_assignments(mut self) -> Result<Self> {
        if !self.kinetics.is_empty() {
            return Err(ModcxxError::InternalError(
                "Dead assignments must run after KINETIC -> SPARSE elaboration".to_string(),
            ));
        }
        if !self.procedures.is_empty() {
            return Err(ModcxxError::InternalError(
                "Dead assignments must run after PROCEDURE inlining".to_string(),
            ));
        }

        fn is_first_read_in(var: &str, stmnts: &[Statement]) -> Result<bool> {
            for stmnt in stmnts {
                match &stmnt.data {
                    StatementT::Assign(lhs, rhs) => {
                        if rhs.uses().is_read(var).is_some() {
                            return Ok(true);
                        }
                        if lhs == var {
                            return Ok(false);
                        }
                    }
                    StatementT::Return(exp) => {
                        if exp.uses().is_read(var).is_some() {
                            return Ok(true);
                        }
                    }
                    StatementT::Conserve(lhs, rhs) => {
                        if lhs.uses().is_used(var) {
                            return Ok(true);
                        }
                        if rhs.uses().is_used(var) {
                            return Ok(true);
                        }
                    }
                    StatementT::Linear(lhs, rhs) => {
                        if lhs.uses().is_used(var) {
                            return Ok(true);
                        }
                        if rhs.uses().is_used(var) {
                            return Ok(true);
                        }
                    }
                    StatementT::Derivative(lhs, rhs) => {
                        if rhs.uses().is_used(var) {
                            return Ok(true);
                        }
                        if &format!("{var}'") == lhs {
                            return Ok(false);
                        }
                    }
                    StatementT::Solve(_, _) => {}
                    StatementT::IfThenElse(c, t, e) => {
                        if c.uses().is_read(var).is_some() {
                            return Ok(true);
                        }
                        if is_first_read_in(var, &t.data.stmnts)? {
                            return Ok(true);
                        }
                        if let Some(e) = e {
                            if is_first_read_in(var, &e.data.stmnts)? {
                                return Ok(true);
                            }
                        }
                    }
                    StatementT::Block(blk) => {
                        if is_first_read_in(var, &blk.data.stmnts)? {
                            return Ok(true);
                        }
                    }
                    StatementT::Call(_, args) => {
                        if args.iter().any(|exp| exp.uses().is_read(var).is_some()) {
                            return Ok(true);
                        }
                    }
                    StatementT::Rate(_, _, _, _) => {
                        return Err(ModcxxError::InternalError(
                            "Dataflow called before KINETIC -> SPARSE elaboration".to_string(),
                        ));
                    }
                    StatementT::Initial(_) => {
                        return Err(ModcxxError::InternalError(
                            "Dataflow called on invalid AST".to_string(),
                        ));
                    }
                }
            }
            Ok(false)
        }

        fn strip(blk: &mut Block) -> Result<()> {
            let mut new = Vec::new();
            for (ix, stmnt) in blk.stmnts.iter().enumerate() {
                if let StatementT::Assign(lhs, _) = &stmnt.data {
                    if blk.locals.iter().any(|v| &v.name == lhs)
                        && !is_first_read_in(lhs, &blk.stmnts[ix + 1..])?
                    {
                        continue;
                    }
                }
                new.push(stmnt.clone());
            }
            blk.stmnts = new;
            Ok(())
        }

        if let Some(ref mut blk) = self.initial {
            strip(&mut blk.body)?;
        }

        if let Some(ref mut blk) = self.breakpoint {
            strip(&mut blk.body)?;
        }

        if let Some(ref mut blk) = self.net_receive {
            strip(&mut blk.body)?;
        }

        for blk in self.derivatives.iter_mut() {
            strip(&mut blk.body)?;
        }

        Ok(self)
    }
}

/// Given a function body, its dummy args, and the actual arguments;
/// produce a block to effectively inline the function. If a `return`
/// statement is included, replace it with an assignment to
/// `function-name_line-of-call-col-of-call`.
fn inline_body(
    name: &str,
    dummy: &[String],
    body: &Block,
    args: &[Expression],
    loc: Location,
) -> Result<Statement> {
    let lut = body
        .locals
        .iter()
        .map(|l| {
            (
                l.name.clone(),
                format!("{}_{}_{}", l.name, loc.line, loc.column),
            )
        })
        .collect::<Map<String, String>>();
    let mut body = Statement::block(body.clone());
    let mut extra_locals = Set::new();
    body = body.substitute_if(&mut |s: &Statement| {
        if let StatementT::Return(rhs) = &s.data {
            let local = format!("call_{name}_{}_{}", loc.line, loc.column);
            extra_locals.insert(local.clone());
            Some(Statement::assign(&local, rhs.clone(), s.loc))
        } else {
            None
        }
    })?;
    let StatementT::Block(ref mut inner) = &mut body.data else {
        unreachable!();
    };
    inner
        .locals
        .extend(extra_locals.iter().map(|n| Symbol::local(n, body.loc)));
    body = body.rename_all(&lut)?;
    for (f, t) in dummy.iter().zip(args.iter()) {
        body = body.substitute(&ExpressionT::Variable(f.to_string()), t)?;
    }

    Ok(body)
}

fn inline_procedure_into_block(
    blk: &Block,
    procs: &Map<String, (Vec<String>, Block)>,
) -> Result<Block> {
    let mut depth = 0;
    let mut blk = blk.clone();
    loop {
        let mut new = Vec::new();
        for stmnt in blk.stmnts.iter() {
            let loc = stmnt.loc;
            let stmnt = match &stmnt.data {
                StatementT::Call(cname, cargs) if procs.contains_key(cname) => {
                    let (pargs, pbody) = &procs[cname];
                    inline_body(cname, pargs, pbody, cargs, loc)?
                }
                StatementT::IfThenElse(c, t, e) => {
                    let t = inline_procedure_into_block(t, procs)?;
                    let e = if let Some(e) = e {
                        Some(inline_procedure_into_block(e, procs)?)
                    } else {
                        None
                    };
                    Statement::if_then_else(c.clone(), t, e, loc)
                }
                StatementT::Block(blk) => {
                    Statement::block(inline_procedure_into_block(blk, procs)?)
                }
                _ => stmnt.clone(),
            };
            new.push(stmnt);
        }
        if new == blk.stmnts {
            break;
        }
        if depth > 10 {
            unimplemented!(); // Recursion depth!
        }
        blk.stmnts = new;
        depth += 1;
    }
    Ok(blk)
}

fn inline_function_into_block(
    blk: &Block,
    procs: &Map<String, (Vec<String>, Block)>,
) -> Result<Block> {
    let mut depth = 0;
    let mut blk = blk.clone();
    loop {
        let mut new = Vec::new();
        for stmnt in blk.stmnts.iter() {
            let mut pred = |ex: &Expression| {
                if let ExpressionT::Call(f, args) = &ex.data {
                    if let Some((dummy, body)) = procs.get(f) {
                        new.push(inline_body(f, dummy, body, args, ex.loc).unwrap());
                        Some(Expression::variable(
                            &format!("call_{f}_{}_{}", ex.loc.line, ex.loc.column),
                            ex.loc,
                        ))
                    } else {
                        None
                    }
                } else {
                    None
                }
            };
            let loc = stmnt.loc;
            match &stmnt.data {
                StatementT::Assign(lhs, rhs) => {
                    let rhs = rhs.substitute_if(&mut pred)?;
                    new.push(Statement::assign(lhs, rhs, loc));
                }
                StatementT::IfThenElse(c, t, e) => {
                    let c = c.substitute_if(&mut pred)?;
                    let t = inline_function_into_block(t, procs)?;
                    let e = if let Some(e) = e {
                        Some(inline_function_into_block(e, procs)?)
                    } else {
                        None
                    };
                    new.push(Statement::if_then_else(c, t, e, loc));
                }
                StatementT::Derivative(lhs, rhs) => {
                    let rhs = rhs.substitute_if(&mut pred)?;
                    new.push(Statement::derivative(lhs, rhs, loc));
                }
                StatementT::Return(rhs) => {
                    let rhs = rhs.substitute_if(&mut pred)?;
                    new.push(Statement::ret(rhs, loc));
                }
                StatementT::Conserve(lhs, rhs) => {
                    let lhs = lhs.substitute_if(&mut pred)?;
                    let rhs = rhs.substitute_if(&mut pred)?;
                    new.push(Statement::conserve(lhs, rhs, loc));
                }
                StatementT::Rate(lhs, rhs, fwd, bwd) => {
                    let lhs = lhs.substitute_if(&mut pred)?;
                    let rhs = rhs.substitute_if(&mut pred)?;
                    let fwd = fwd.substitute_if(&mut pred)?;
                    let bwd = bwd.substitute_if(&mut pred)?;
                    new.push(Statement::rate(lhs, rhs, fwd, bwd, loc));
                }
                StatementT::Linear(lhs, rhs) => {
                    let lhs = lhs.substitute_if(&mut pred)?;
                    let rhs = rhs.substitute_if(&mut pred)?;
                    new.push(Statement::linear(lhs, rhs, loc));
                }
                StatementT::Initial(inner) => new.push(Statement::initial(
                    inline_function_into_block(inner, procs)?,
                    loc,
                )),
                StatementT::Block(inner) => {
                    new.push(Statement::block(inline_function_into_block(inner, procs)?))
                }
                StatementT::Call(_, _) | StatementT::Solve(_, _) => new.push(stmnt.clone()),
            }
        }
        if new == blk.stmnts {
            break;
        }
        if depth > 10 {
            unimplemented!(); // Recursion depth!
        }
        blk.stmnts = new;
        depth += 1;
    }
    Ok(blk)
}

fn check_duplicates_and_keywords(module: &Module) -> Result<()> {
    fn check(name: &str, loc: Location, seen: &mut Map<String, Location>) -> Result<()> {
        if let Some(old) = seen.get(name) {
            return Err(ModcxxError::DuplicateSymbol(name.to_string(), loc, *old));
        }
        if KEYWORDS.iter().any(|p| p.0 == name) {
            return Err(ModcxxError::ReservedWord(name.to_string(), loc));
        }
        seen.insert(name.to_string(), loc);
        Ok(())
    }

    let ionic = module
        .ions
        .iter()
        .flat_map(|i| i.vars.iter())
        .cloned()
        .collect::<Vec<_>>();

    let assigned = module
        .assigned
        .iter()
        .filter(|v| {
            !module
                .non_specific_currents
                .iter()
                .any(|s| s.name == v.name)
        })
        .filter(|v| !ionic.iter().any(|s| s.name == v.name))
        .cloned()
        .collect::<Vec<_>>();

    let parameters = module
        .parameters
        .iter()
        .filter(|v| {
            !module
                .non_specific_currents
                .iter()
                .any(|s| s.name == v.name)
        })
        .filter(|v| !ionic.iter().any(|s| s.name == v.name))
        .cloned()
        .collect::<Vec<_>>();

    let mut seen = Map::new();
    for items in &[
        &module.non_specific_currents,
        &assigned,
        &ionic,
        &parameters,
        &module.constants,
    ] {
        for item in items.iter() {
            check(&item.name, item.loc, &mut seen)?;
        }
    }

    for items in &[
        &module.derivatives,
        &module.kinetics,
        &module.functions,
        &module.procedures,
    ] {
        for item in items.iter() {
            check(&item.name, item.loc, &mut seen)?;
        }
    }

    Ok(())
}

fn check_scope(
    uses: &Inventory,
    globals: &Map<String, Access>,
    solvables: &Set<String>,
    functions: &Map<String, usize>,
) -> Result<()> {
    for (var, n) in functions {
        if let Some(e) = uses.is_read(var).or(uses.is_written(var)) {
            return Err(ModcxxError::CallableNotVariable(var.to_string(), e.src));
        }
        if let Some(e) = uses.is_solved(var) {
            return Err(ModcxxError::CallableNotSolvable(var.to_string(), e.src));
        }
        if let Some(es) = uses.get(var) {
            for e in es.calls.iter() {
                if *n != e.args {
                    return Err(ModcxxError::WrongArity(var.to_string(), *n, e.args, e.src));
                }
            }
        }
    }
    for (var, acc) in globals.iter() {
        if let Some(e) = uses.is_called(var) {
            return Err(ModcxxError::VariableNotCallable(var.to_string(), e.src));
        }
        if let Some(e) = uses.is_solved(var) {
            return Err(ModcxxError::VariableNotSolvable(var.to_string(), e.src));
        }
        if *acc == Access::RO {
            if let Some(e) = uses.is_written_kind(var, usr::Kind::Global) {
                return Err(ModcxxError::WriteToRO(var.to_string(), e.src));
            }
        }
    }
    for var in solvables.iter() {
        if let Some(e) = uses.is_read(var).or(uses.is_written(var)) {
            return Err(ModcxxError::SolvableNotVariable(var.to_string(), e.src));
        }
        if let Some(e) = uses.is_called(var) {
            return Err(ModcxxError::SolvableNotCallable(var.to_string(), e.src));
        }
    }

    for k in uses.0.keys() {
        if let Some(e) = uses
            .is_solved(k)
            .or(uses.is_called(k))
            .or(uses.is_read_kind(k, usr::Kind::Global))
            .or(uses.is_written_kind(k, usr::Kind::Global))
        {
            if !globals.contains_key(k) && !solvables.contains(k) && !functions.contains_key(k) {
                return Err(ModcxxError::UnboundName(k.to_string(), e.src));
            }
        }
    }

    Ok(())
}

fn check_scopes(module: &Module) -> Result<()> {
    let mut globals = Map::new();
    for g in KNOWN {
        globals.insert(g.0.to_string(), Access::RO);
    }
    for vars in &[
        &module.constants,
        &module.parameters,
        &module.states,
        &module.assigned,
    ] {
        for var in vars.iter() {
            globals.insert(var.name.to_string(), var.access);
        }
    }
    for var in &module.states {
        globals.insert(format!("{}'", var.name), var.access);
    }

    for var in &module.non_specific_currents {
        globals.insert(var.name.to_string(), var.access);
    }

    for ion in &module.ions {
        for var in &ion.vars {
            globals.insert(var.name.to_string(), var.access);
        }
        if let Some(Expression {
            data: ExpressionT::Variable(v),
            ..
        }) = &ion.vale
        {
            globals.insert(v.to_string(), Access::RO);
        }
    }

    let mut funcs = FUNCTIONS
        .iter()
        .map(|(k, v)| (k.to_string(), *v))
        .collect::<Map<String, usize>>();
    for items in &[
        //&module.kinetics, NO! not this
        &module.procedures,
        &module.functions,
    ] {
        for item in items.iter() {
            funcs.insert(
                item.name.to_string(),
                item.args.as_deref().map_or(0, |args| args.len()),
            );
        }
    }

    let mut solves = Set::new();
    for items in &[&module.linears, &module.kinetics, &module.derivatives] {
        for item in items.iter() {
            solves.insert(item.name.to_string());
        }
    }

    for items in &[
        &module.derivatives,
        &module.kinetics,
        &module.functions,
        &module.linears,
        &module.procedures,
    ] {
        for item in items.iter() {
            check_scope(&item.uses(), &globals, &solves, &funcs)?;
        }
    }

    for item in &[&module.breakpoint, &module.initial, &module.net_receive] {
        if let Some(f) = item {
            check_scope(&f.uses(), &globals, &solves, &funcs)?;
        }
    }

    Ok(())
}
/// Take a series of KINETIC reaction statements like
///   ~ aX + bY <-> cZ (kf, kb)
/// and produce a sparse ODE system.
/// First we elaborate the reversible reaction to
/// ~ aX + bY -- kf --> cZ
/// ~ cZ      -- kb --> aX + bY
/// Second, we compute the reaction rates
///   rf = kf X^a Y^b
///   rb = kb Z^c
/// and, third, write out the system of ODEs
///   X' = -a rf + a rb = a (rb - rf)
///   Y' =                b (rb - rf)
///   Z' =                c (rb - rf)
/// by way of the Law of Mass Action.
/// In general, if we are given
///  ---                      ---
///  >    n   X   -- k_j -->  >    m    X
///  ---   ij  i              ---   ij   i
///   i                        i
/// the rates are
///           ----- n_ij
///   r  = k   | | X
///    j    j  | |  i
///             i
/// and the ODEs are
///       ---
/// X'  = >    (m   - n  ) r
///  i    ---    ij    ij   j
///        i
/// NOTE: We collect all statements by type, thus
/// KINETIC foobar {
///    LOCAL x, y
///
///    x = 23*v
///    y = 42*v
///
///    ~ A <-> B (x, y)
///
///    x = sin(y)
///    y = cos(x)
///
///    ~ C <-> D (x, y)
///  }
///
/// effectively is
///
/// KINETIC foobar {
///   LOCAL x, y
///
///   x = 23*v
///   y = 42*v
///   x = sin(y)
///   y = cos(x)
///
///   ~ A <-> B (x, y)
///   ~ C <-> D (x, y)
/// }
///
/// this is handled **the same** in nmodl/modcc, but _should_
/// be an error. Bug-for-bug compatible, I guess.
/// NOTE: What we really should be doing here is this
///
/// KINETIC foobar {
///   LOCAL x, y, x2 y2
///
///   x = 23*v
///   y = 42*v
///   x2 = sin(y)
///   y2 = cos(x)
///
///   ~ A <-> B (x, y)
///   ~ C <-> D (x2, y2)
/// }
///
/// Even worse is this
///
/// KINETIC foobar {
///   LOCAL x, y
///
///   x = 23*v
///   y = 42*v
///
///   if (v<0) {
///     ~ A <-> B (x, y)
///   } else {
///     ~ C <-> D (y, x)
///   }
/// }
///
/// which an error in modcc, but nmodl produces
///
/// KINETIC foobar {
///   LOCAL x, y,
///
///   x = 23*v
///   y = 42*v
///
///   if (v<0) {
///   } else {
///   }
///   ~ A <-> B (x, y)
///   ~ C <-> D (y, x)
/// }
///
/// Yes, really. Proper here should be this:
///
/// KINETIC foobar {
///   LOCAL x, y, kAB, iAB, kCD, iCD
///
///   kAB = iAB = kCD = iCD = 0
///   x = 23*v
///   y = 42*v
///
///   if (v<0) {
///     kAB = x
///     iAB = y
///   } else {
///     kCD = y
///     iCD = x
///   }
///   ~ A <-> B (kAB, iAB)
///   ~ C <-> D (kCD, iCD)
/// }
///
/// but this subject to combinatoric explosion and can lead to
/// extremely large systems!
fn kinetic_to_sparse(kin: Callable) -> Result<Callable> {
    // Temporary fix until we parse stoich terms correctly.
    fn extract_stoich(ex: &Expression) -> Vec<(Expression, Expression)> {
        let mut res = Vec::new();
        let mut todo = vec![ex.clone()];
        while let Some(Expression { ref data, loc }) = todo.pop() {
            match data {
                v @ ExpressionT::Variable(_) => {
                    res.push((
                        Expression::number("1", Location::default()),
                        Expression {
                            data: v.clone(),
                            loc,
                        },
                    ));
                }
                ExpressionT::Binary(l, Operator::Mul, r) => {
                    let n = if let ExpressionT::Number(_) = &l.data {
                        l.clone()
                    } else {
                        panic!()
                    };
                    let v = if let ExpressionT::Variable(_) = &r.data {
                        r.clone()
                    } else {
                        panic!()
                    };
                    res.push((*n, *v));
                }
                ExpressionT::Binary(l, Operator::Add, r) => {
                    todo.push(*r.clone());
                    todo.push(*l.clone());
                }
                ExpressionT::Binary(l, Operator::Sub, r) => {
                    todo.push(*r.clone());
                    todo.push(*l.clone());
                }
                _ => panic!("Unexpected: {data:?}"),
            }
        }
        res
    }

    let mut reactions = Vec::new();
    let mut stmnts = Vec::new();

    #[derive(PartialEq, Eq)]
    enum State {
        Normal,
        Reaction,
    }

    let mut last = State::Normal;
    for stmnt in &kin.body.stmnts {
        match &stmnt.data {
            StatementT::Linear(_, _) => {
                return Err(ModcxxError::StatementUnsupported(
                    "LINEAR".into(),
                    "KINETIC".into(),
                    stmnt.loc,
                ))
            }
            StatementT::Derivative(_, _) => {
                return Err(ModcxxError::StatementUnsupported(
                    "DERIVATIVE".into(),
                    "KINETIC".into(),
                    stmnt.loc,
                ))
            }
            StatementT::Rate(l, r, f, b) => {
                last = State::Reaction;
                let lhs = extract_stoich(l);
                let rhs = extract_stoich(r);
                reactions.push((lhs, rhs, f.clone(), b.clone()));
            }
            StatementT::Conserve(_, _) => {
                last = State::Reaction;
            }
            _ => {
                if last == State::Reaction {
                    // TODO: Gather up all Assignments v = k here, rename v to v_2, then substitute
                    // v -> v_2 in all downstream statements.
                    // TODO: Go nuts if we encounter a conditional...
                    return Err(ModcxxError::IntermingledReactionNormal(stmnt.loc));
                }
                stmnts.push(stmnt.clone());
            }
        }
    }

    let mut deriv = Map::new();
    for (lhs, rhs, rf, rb) in &reactions {
        // rates
        let mut rate_fw = rf.clone();
        for (n, v) in lhs {
            rate_fw = Expression::mul(
                rate_fw,
                Expression::pow(v.clone(), n.clone(), Location::default()),
                Location::default(),
            );
        }

        let mut rate_bw = rb.clone();
        for (n, v) in rhs {
            rate_bw = Expression::mul(
                rate_bw,
                Expression::pow(v.clone(), n.clone(), Location::default()),
                Location::default(),
            );
        }

        for (n, v) in lhs {
            let k = if let ExpressionT::Variable(v) = &v.data {
                v.clone()
            } else {
                panic!()
            };
            deriv
                .entry(k.clone())
                .or_insert_with(Vec::new)
                .push(Expression::neg(
                    Expression::mul(rate_fw.clone(), n.clone(), Location::default()),
                    Location::default(),
                ));
            deriv
                .entry(k)
                .or_insert_with(Vec::new)
                .push(Expression::mul(
                    rate_bw.clone(),
                    n.clone(),
                    Location::default(),
                ));
        }
        for (n, v) in rhs {
            let k = if let ExpressionT::Variable(v) = &v.data {
                v.clone()
            } else {
                panic!()
            };
            deriv
                .entry(k.clone())
                .or_insert_with(Vec::new)
                .push(Expression::neg(
                    Expression::mul(rate_bw.clone(), n.clone(), Location::default()),
                    Location::default(),
                ));
            deriv
                .entry(k)
                .or_insert_with(Vec::new)
                .push(Expression::mul(
                    rate_fw.clone(),
                    n.clone(),
                    Location::default(),
                ));
        }
    }

    for (k, mut vs) in deriv.into_iter() {
        let mut rhs = if let Some(v) = vs.pop() {
            v.clone()
        } else {
            continue;
        };
        while let Some(v) = vs.pop() {
            rhs = Expression::add(rhs, v, Location::default());
        }
        stmnts.push(Statement::derivative(&k, rhs, Location::default()));
    }
    let mut body = Block::block(&kin.body.locals, &stmnts, kin.body.loc);
    body = body.simplify()?;
    Ok(Callable::procedure(&kin.name, &[], None, body, kin.loc))
}

impl Simplify for Module {
    fn simplify(&self) -> Result<Self> {
        let mut res = self.clone();
        for ps in &mut [
            &mut res.kinetics,
            &mut res.procedures,
            &mut res.derivatives,
            &mut res.functions,
        ] {
            for p in ps.iter_mut() {
                *p = p.simplify()?;
            }
        }
        for op in &mut [&mut res.breakpoint, &mut res.initial, &mut res.net_receive] {
            if let Some(ref mut p) = op {
                *p = p.simplify()?;
            }
        }
        Ok(res)
    }
}

#[cfg(test)]
mod tests {
    use crate::{ast, nmd::to_nmodl};

    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_arity() {
        let s = par::parse(
            "
NEURON { SUFFIX test }

INITIAL { LOCAL x
   x = exp(x, x)
 }

BREAKPOINT {}
",
        )
        .unwrap();
        let m = Module::new(&s);
        assert!(matches!(m, Err(ModcxxError::WrongArity(f, 1, 2, _)) if f == "exp"));
    }

    #[test]
    fn test_req_blocks() {
        let s = par::parse(
            "
NEURON { SUFFIX test }
",
        )
        .unwrap();
        let m = Module::new(&s);
        assert!(matches!(m, Err(ModcxxError::MissingBlock(f)) if f == "BREAKPOINT"));

        let s = par::parse(
            "
NEURON {}
",
        )
        .unwrap();
        let m = Module::new(&s);
        assert_eq!(m, Err(ModcxxError::MissingKind));

        let s = par::parse(
            "
BREAKPOINT {}
",
        )
        .unwrap();
        let m = Module::new(&s);
        assert!(matches!(m, Err(ModcxxError::MissingBlock(f)) if f == "NEURON"));
    }

    #[test]
    fn test_dup_blocks() {
        let s = par::parse(
            "
NEURON { SUFFIX test }

INITIAL {}

BREAKPOINT {}
BREAKPOINT {}
",
        )
        .unwrap();
        let m = Module::new(&s);
        assert!(matches!(m, Err(ModcxxError::DuplicateBlock(f, _, _)) if f == "BREAKPOINT"));

        let s = par::parse(
            "
NEURON { SUFFIX test }
NEURON { SUFFIX test }

INITIAL {}

BREAKPOINT {}
",
        )
        .unwrap();
        let m = Module::new(&s);
        assert!(matches!(m, Err(ModcxxError::DuplicateBlock(f, _, _)) if f == "NEURON"));

        let s = par::parse(
            "
NEURON { SUFFIX test }

INITIAL {}
INITIAL {}

BREAKPOINT {}
",
        )
        .unwrap();
        let m = Module::new(&s);
        assert!(matches!(m, Err(ModcxxError::DuplicateBlock(f, _, _)) if f == "INITIAL"));

        let s = par::parse(
            "
NEURON { SUFFIX test }

INITIAL {}

BREAKPOINT {}

NET_RECEIVE() {}
NET_RECEIVE() {}
",
        )
        .unwrap();
        let m = Module::new(&s);
        assert!(matches!(m, Err(ModcxxError::DuplicateBlock(f, _, _)) if f == "NET_RECEIVE"));
    }

    #[test]
    fn dead_statements() {
        let s = par::parse(
            "
NEURON { SUFFIX test }

INITIAL {}

BREAKPOINT { foo() }

FUNCTION foo() {
  foo = 42
}
",
        )
        .unwrap();
        let m = Module::new(&s).unwrap().eliminate_dead_calls().unwrap();
        assert!(m.breakpoint.unwrap().body.data.stmnts.is_empty());
    }

    #[test]
    fn inline_function() {
        let s = par::parse(
            "
NEURON { SUFFIX test }

INITIAL {}

STATE { s }

BREAKPOINT { s = foo() }

FUNCTION foo() {
  foo = 42
}
",
        )
        .unwrap();
        let s = &ast::Module::new(&s)
            .unwrap()
            .inline_functions()
            .unwrap()
            .splat_blocks()
            .unwrap()
            .breakpoint
            .unwrap()
            .body;

        assert_eq!(
            s.locals,
            vec![Symbol::local(
                "call_foo_7_17",
                Location {
                    line: 9,
                    column: 15,
                    position: 91
                }
            ),]
        );
        assert_eq!(
            s.stmnts.last().unwrap(),
            &Statement::assign(
                "s",
                Expression::variable(
                    "call_foo_7_17",
                    Location {
                        line: 7,
                        column: 17,
                        position: 67
                    }
                ),
                Location {
                    line: 7,
                    column: 15,
                    position: 65
                }
            )
        );
        let s = par::parse(
            "
NEURON { SUFFIX test }

INITIAL {}

STATE { s }

BREAKPOINT { s = foo(2) * foo(1) }

FUNCTION foo(n) {
  foo = n + 42
}
",
        )
        .unwrap();
        let s = &ast::Module::new(&s)
            .unwrap()
            .inline_functions()
            .unwrap()
            .splat_blocks()
            .unwrap()
            .breakpoint
            .unwrap()
            .body;

        assert_eq!(
            s.locals,
            vec![
                Symbol::local(
                    "call_foo_7_17",
                    Location {
                        line: 9,
                        column: 16,
                        position: 102
                    }
                ),
                Symbol::local(
                    "call_foo_7_26",
                    Location {
                        line: 9,
                        column: 16,
                        position: 102
                    }
                ),
            ]
        );
        assert_eq!(
            s.stmnts.last().unwrap(),
            &Statement::assign(
                "s",
                Expression::mul(
                    Expression::variable(
                        "call_foo_7_17",
                        Location {
                            line: 7,
                            column: 17,
                            position: 67
                        }
                    ),
                    Expression::variable(
                        "call_foo_7_26",
                        Location {
                            line: 7,
                            column: 26,
                            position: 76
                        }
                    ),
                    Location {
                        line: 7,
                        column: 24,
                        position: 74
                    }
                ),
                Location {
                    line: 7,
                    column: 15,
                    position: 65
                }
            )
        );
    }

    #[test]
    fn cnexp_solver() {
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
        let s = &ast::Module::new(&s)
            .unwrap()
            .solve_odes()
            .unwrap()
            .splat_blocks()
            .unwrap();
        assert_eq!(
            s.breakpoint.as_ref().unwrap().body.stmnts.last().unwrap(),
            &Statement::assign(
                "s",
                Expression::neg(
                    Expression::variable(
                        "ba_",
                        Location {
                            line: 0,
                            column: 0,
                            position: 0
                        }
                    ),
                    Location {
                        line: 0,
                        column: 0,
                        position: 0
                    }
                ),
                Location {
                    line: 0,
                    column: 0,
                    position: 0
                }
            ),
        );

        let t = par::parse(
            "
NEURON { SUFFIX test }

INITIAL {}

STATE { s }

BREAKPOINT { SOLVE dS }

DERIVATIVE dS {
  s' = 42*s + 23
}
",
        )
        .unwrap();
        let t = &ast::Module::new(&t)
            .unwrap()
            .solve_odes()
            .unwrap()
            .splat_blocks()
            .unwrap();
        assert_eq!(t, s);

        let s = par::parse(
            "
NEURON { SUFFIX test }

INITIAL {}

STATE { s }

BREAKPOINT { SOLVE dS METHOD cnexp }

DERIVATIVE dS {
  LOCAL x, y
  x = 23
  y = 42
  s' = y*s + x
}
",
        )
        .unwrap();
        let s = &ast::Module::new(&s)
            .unwrap()
            .solve_odes()
            .unwrap()
            .splat_blocks()
            .unwrap();
        eprintln!("{}", to_nmodl(s).unwrap());

        let s = par::parse(
            "
NEURON { SUFFIX test }

INITIAL {}

STATE { s t }

BREAKPOINT { SOLVE dS METHOD cnexp }

DERIVATIVE dS {
  LOCAL x, y, u, w
  x = 23
  y = 42
  s' = y*s + x
  t' = u*t + v
}
",
        )
        .unwrap();
        let s = &ast::Module::new(&s)
            .unwrap()
            .solve_odes()
            .unwrap()
            .splat_blocks()
            .unwrap();
        eprintln!("{}", to_nmodl(s).unwrap());
    }
}
