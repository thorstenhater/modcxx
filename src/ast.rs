use crate::{
    err::{ModcxxError, Result},
    exp::{
        Access, Block, Callable, Expression, ExpressionT, Operator, Statement, StatementT, Symbol,
        Unit, Use,
    },
    lex::KEYWORDS,
    opt::Simplify,
    par::{self, Ion, Kind},
    src::Location,
    Map, Set,
};

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
    pub units: Vec<(Unit, Unit)>,
    pub procedures: Vec<Callable>,
    pub kinetics: Vec<Callable>,
    pub linears: Vec<Callable>,
    pub functions: Vec<Callable>,
    pub constants: Vec<Symbol>,
    pub net_receive: Option<Callable>,
}

pub const FUNCTIONS: [(&'static str, usize); 1] = [("exp", 1)];
pub const KNOWN: [(&'static str, &'static str); 4] = [("celsius", "degC"),
                                                      ("v", "mV"),
                                                      ("area", "um2"),
                                                      ("diam", "um"),];


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
        let mut ranges = nrn.ranges.clone();
        let globals = nrn.globals.clone();

        let states = module.states.clone();
        // STATE and ions are module local anyhow.
        ranges.retain(|r| !states.iter().any(|s| &s.name == r));
        ranges.retain(|r| !ions.iter().any(|s| &s.name == r));

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
            eprintln!("ASSIGNED {nm}");
            if !ranges.contains(nm) && !globals.contains(nm) && !KNOWN.iter().any(|p| p.0 == nm) {
                eprintln!("++ ASSIGNED {nm}");
                ranges.push(nm.to_string());
            }
        }

        let derivatives = module.derivatives.clone();
        let assigned = module.assigned.clone();
        let units = module.units.clone();
        let constants = module.constants.clone();
        let functions = module.functions.clone();
        let procedures = module.procedures.clone();
        let parameters = module.parameters.clone();
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

    pub fn eliminate_dead_blocks(mut self) -> Result<Self> {
        // Let's figure out some data flow
        let mut used = Map::new();
        // NET_RECEIVE, INITIAL, and BREAKPOINT are our entry points
        for blk in &[&self.initial, &self.breakpoint, &self.net_receive] {
            if let Some(blk) = blk {
                for (k, mut v) in blk.uses().into_iter() {
                    used.entry(k).or_insert_with(Set::new).append(&mut v);
                }
            }
        }

        // Weed out vacuous blocks
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

        let mut void = Set::new();
        for ps in &[&self.procedures, &self.linears, &self.kinetics] {
            for p in ps.iter() {
                if p.data.body.stmnts.is_empty() {
                    void.insert(p.name.to_string());
                }
            }
        }

        used.retain(|k, _| !void.contains(k));

        // Now recurse into procedures, functions, derivatives, and kinetics.
        // and iterate towards a fixed point to get transitive calls.
        loop {
            let mut new = used.clone();
            for (k, v) in &used {
                if void.contains(k) {
                    continue;
                }
                if v.contains(&Use::Solve) {
                    let blk = self
                        .kinetics
                        .iter()
                        .find_map(|s| if &s.name == k { Some(s.uses()) } else { None })
                        .unwrap_or(Map::new());
                    for (q, mut w) in blk.into_iter() {
                        new.entry(q).or_insert_with(Set::new).append(&mut w);
                    }
                    let blk = self
                        .derivatives
                        .iter()
                        .find_map(|s| if &s.name == k { Some(s.uses()) } else { None })
                        .unwrap_or(Map::new());
                    for (q, mut w) in blk.into_iter() {
                        new.entry(q).or_insert_with(Set::new).append(&mut w);
                    }
                }
                if v.iter().any(|it| matches!(it, Use::CallP(_))) {
                    let blk = self
                        .procedures
                        .iter()
                        .find_map(|s| if &s.name == k { Some(s.uses()) } else { None })
                        .unwrap_or(Map::new());
                    for (q, mut w) in blk.into_iter() {
                        new.entry(q).or_insert_with(Set::new).append(&mut w);
                    }
                }
                if v.iter().any(|it| matches!(it, Use::CallF(_))) {
                    let blk = self
                        .functions
                        .iter()
                        .find_map(|s| if &s.name == k { Some(s.uses()) } else { None })
                        .unwrap_or(Map::new());
                    for (q, mut w) in blk.into_iter() {
                        new.entry(q).or_insert_with(Set::new).append(&mut w);
                    }
                }
            }

            if new == used {
                break;
            }
            used = new;

            self.derivatives.retain(|blk| used.contains_key(&blk.name));
            self.procedures.retain(|blk| used.contains_key(&blk.name));
            self.kinetics.retain(|blk| used.contains_key(&blk.name));
            self.functions.retain(|blk| used.contains_key(&blk.name));
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
                inline_into_block(&mut symbol.body, &procs)?;
            }
        }

        for blk in &mut [&mut self.initial, &mut self.breakpoint] {
            if let Some(ref mut proc) = blk {
                inline_into_block(&mut proc.body, &procs)?;
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
                inline_into_block(&mut symbol.body, &procs)?;
            }
        }

        for blk in [&mut self.initial, &mut self.breakpoint].iter_mut() {
            if let Some(ref mut proc) = blk {
                inline_into_block(&mut proc.body, &procs)?;
            }
        }

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

    /// This pass iteratively eliminates dead statements in all blocks. Currently
    /// only works on completely inlined programs.
    /// Two kinds of statements are considered 'dead':
    /// - those never read (after being written)
    /// - those written again before beging read
    pub fn eliminate_dead_statements(mut self) -> Result<Self> {
        fn should_keep(lhs: &str, stmnts: &[Statement]) -> Option<bool> {
            for other in stmnts {
                if let Some(us) = other.uses().get(lhs) {
                    // NOTE: in this statement
                    //   x = x + 42
                    // we get both a READ and a WRITE, but the READ occurs
                    // first, so we need to keep it.
                    // next statment was a READ, so we have to keep it.
                    if us.contains(&Use::R) {
                        return Some(true);
                    }
                    // next statment was a WRITE, so we can discard.
                    if us.contains(&Use::W) {
                        return Some(false);
                    }
                }
            }
            None
        }

        fn eliminate_in_proc(
            proc: &Callable,
            breakpoint: &Option<Callable>,
            net_receive: &Option<Callable>,
            kinetics: &[Callable],
            derivatives: &[Callable],
            must_keep: &[String],
        ) -> Callable {
            let mut new = Vec::new();
            // NOTE alphatised programs would be a nice thing...
            for (ix, stmnt) in proc.body.stmnts.iter().enumerate() {
                if let StatementT::Assign(lhs, _) = &stmnt.data {
                    if must_keep.contains(lhs) {
                        new.push(stmnt.clone());
                        continue;
                    }
                    let keep_local = should_keep(lhs, &proc.body.stmnts[ix + 1..]);
                    // for non-locals we have to scan more blocks
                    // * BREAKPOINT
                    //   * if present check SOLVEd KINETICs and DERIVATIVEs in order of mention
                    //   * then the body of BREAKPOINT
                    let keep_break = if !proc.body.locals.iter().any(|s| &s.name == lhs) {
                        let mut keep = None;
                        if let Some(proc) = &breakpoint {
                            for stmnt in &proc.body.stmnts {
                                if let StatementT::Solve(blk, _) = &stmnt.data {
                                    if let Some(d) = derivatives.iter().find(|p| &p.name == blk) {
                                        keep = keep.or(should_keep(lhs, &d.body.stmnts));
                                    }
                                    if let Some(k) = kinetics.iter().find(|p| &p.name == blk) {
                                        keep = keep.or(should_keep(lhs, &k.body.stmnts));
                                    }
                                }
                            }
                            keep = keep.or(should_keep(lhs, &proc.body.stmnts));
                        }
                        keep
                    } else {
                        None
                    };
                    // NET_RECEIVE *might* be interjected between two BREAKPOINTs.
                    let keep_recv = if !proc.body.locals.iter().any(|s| &s.name == lhs) {
                        let mut keep = None;
                        if let Some(proc) = net_receive {
                            keep = keep.or(should_keep(lhs, &proc.body.stmnts));
                        }
                        keep
                    } else {
                        None
                    };
                    // Combine sub-results
                    let keep = keep_local.or(keep_break).or(keep_recv);
                    // we got to the end, nobody used it ... begone
                    if let Some(true) = keep {
                        new.push(stmnt.clone());
                    }
                } else {
                    new.push(stmnt.clone());
                }
            }

            let mut res = proc.clone();
            res.body.stmnts = new;
            res
        }

        let mut must_keep = Vec::new();
        for ion in &self.ions {
            for var in &ion.vars {
                if var.access == Access::RW {
                    must_keep.push(var.name.to_string());
                }
            }
        }
        for nsc in &self.non_specific_currents {
            must_keep.push(nsc.name.to_string());
        }

        if let Some(ref mut proc) = &mut self.initial {
            loop {
                let new = eliminate_in_proc(
                    proc,
                    &self.breakpoint,
                    &self.net_receive,
                    &self.kinetics,
                    &self.derivatives,
                    &must_keep,
                );
                if &new == proc {
                    break;
                }
                *proc = new;
            }
        }

        if let Some(ref mut proc) = &mut self.breakpoint {
            loop {
                let new = eliminate_in_proc(
                    proc,
                    &Some(proc.clone()),
                    &self.net_receive,
                    &self.kinetics,
                    &self.derivatives,
                    &must_keep,
                );
                if &new == proc {
                    break;
                }
                *proc = new;
            }
        }

        if let Some(ref mut proc) = &mut self.net_receive {
            loop {
                let new = eliminate_in_proc(
                    proc,
                    &self.breakpoint,
                    &Some(proc.clone()),
                    &self.kinetics,
                    &self.derivatives,
                    &must_keep,
                );
                if &new == proc {
                    break;
                }
                *proc = new;
            }
        }

        for proc in self.kinetics.iter_mut() {
            loop {
                let new = eliminate_in_proc(
                    proc,
                    &self.breakpoint,
                    &self.net_receive,
                    &[],
                    &self.derivatives,
                    &must_keep,
                );
                if &new == proc {
                    break;
                }
                *proc = new;
            }
        }

        for proc in self.derivatives.iter_mut() {
            loop {
                let new = eliminate_in_proc(
                    proc,
                    &self.breakpoint,
                    &self.net_receive,
                    &self.kinetics,
                    &[],
                    &must_keep,
                );
                if &new == proc {
                    break;
                }
                *proc = new;
            }
        }

        Ok(self)
    }

    pub fn eliminate_dead_globals(mut self) -> Result<Self> {
        loop {
            let mut used = Map::new();

            if let Some(p) = &self.initial {
                used.append(&mut p.uses());
            }

            if let Some(p) = &self.breakpoint {
                used.append(&mut p.uses());
            }

            if let Some(p) = &self.net_receive {
                used.append(&mut p.uses());
            }

            for p in &self.kinetics {
                used.append(&mut p.uses());
            }

            for p in &self.derivatives {
                used.append(&mut p.uses());
            }

            for p in &self.procedures {
                used.append(&mut p.uses());
            }

            for p in &self.functions {
                used.append(&mut p.uses());
            }

            let old_len = self.assigned.len()
                + self.constants.len()
                + self.parameters.len()
                + self.states.len()
                + self.ions.iter().fold(0, |acc, ion| acc + ion.vars.len())
                + self.ions.len()
                + self.globals.len()
                + self.ranges.len();

            self.assigned.retain(|v| {
                used.get(&v.name)
                    .map(|s| s.contains(&Use::R))
                    .unwrap_or(false)
            });
            self.constants.retain(|v| {
                used.get(&v.name)
                    .map(|s| s.contains(&Use::R))
                    .unwrap_or(false)
            });
            self.parameters.retain(|v| {
                used.get(&v.name)
                    .map(|s| s.contains(&Use::R))
                    .unwrap_or(false)
            });
            self.states.retain(|v| {
                used.get(&v.name)
                    .map(|s| s.contains(&Use::R))
                    .unwrap_or(false)
            });
            self.ions
                .iter_mut()
                .for_each(|ion| ion.vars.retain(|var| used.contains_key(&var.name)));
            self.ions.retain(|ion| !ion.vars.is_empty());
            self.globals
                .retain(|v| used.get(v).map(|s| s.contains(&Use::R)).unwrap_or(false));
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
        // Collect callable and solvable things with globally visible writes
        let mut procs = Map::new();
        for items in &[&self.procedures, &self.linears, &self.kinetics, &self.derivatives] {
            for item in items.iter() {
                procs.insert(item.data.name.to_string(), item);
            }
        }

        fn first_use_of(
            others: &[Statement],
            procs: &Map<String, &Callable>,
        ) -> Map<String, Vec<Use>> {
            fn first_use_of_(
                others: &[Statement],
                procs: &Map<String, &Callable>,
                out: &mut Map<String, Vec<Use>>,
            ) {
                for other in others {
                    // We _still_ do this even despite treating Call below, as the
                    // _arguments_ are used _before_ entering the call
                    for (k, vs) in &other.uses() {
                        // NOTE we enter Read before Writes, eg X = X + 1
                        if vs.contains(&Use::R) {
                            out.entry(k.to_string()).or_default().push(Use::R);
                        }
                        if vs.contains(&Use::W) {
                            out.entry(k.to_string()).or_default().push(Use::W);
                        }
                    }
                    match &other.data {
                        StatementT::Solve(what, _) => {
                            if let Some(what) = procs.get(what) {
                                first_use_of_(&what.data.body.stmnts, procs, out);
                            } else {
                                eprintln!("Couldn't find {what} in table.")
                            }
                        }
                        StatementT::Call(Expression {
                            data: ExpressionT::Call(what, _),
                            ..
                        }) if procs.contains_key(what) => {
                            panic!("Found a call to a PROCEDURE in the localise pass, this is unsound! Please completely inline PROCEDUREs first!");
                        }
                        _ => {}
                    }
                }
            }

            let mut uses = Map::new();
            first_use_of_(others, &procs, &mut uses);
            // Collapse consecutive items
            for vs in uses.values_mut() {
                vs.dedup();
            }
            uses.retain(|_, v| !v.is_empty());
            uses
        }

        let init = if let Some(prc) = self.initial.as_ref() {
            first_use_of(&prc.body.stmnts, &procs)
        } else {
            Map::new()
        };

        let brea = if let Some(prc) = &self.breakpoint {
            first_use_of(&prc.body.stmnts, &procs)
        } else {
            Map::new()
        };

        let recv = if let Some(prc) = &self.net_receive {
            first_use_of(&prc.body.stmnts, &procs)
        } else {
            Map::new()
        };

        let mut eliminated = Set::new();
        for assign in &self.assigned {
            let nm = assign.name.to_string();
            // Condition: Either we write initially to var, ...
            let ini = init.contains_key(&nm) && *init[&nm].first().unwrap() == Use::W;
            let bpi = brea.contains_key(&nm) && *brea[&nm].first().unwrap() == Use::W;
            let rci = recv.contains_key(&nm) && *recv[&nm].first().unwrap() == Use::W;

            // ... never do anything with it, or ...
            let inn = !init.contains_key(&nm);
            let bpn = !brea.contains_key(&nm);
            let rcn = !recv.contains_key(&nm);

            // _read_ a variable
            let inr = init.contains_key(&nm) && init[&nm].contains(&Use::R);
            let bpr = brea.contains_key(&nm) && brea[&nm].contains(&Use::R);
            let rcr = recv.contains_key(&nm) && recv[&nm].contains(&Use::R);

            // We have some cases here: The variable is...
            // 1. always written before being read => localise
            // 2. never used => eliminate
            // 3. written in INITIAL and consumed in later blocks. We _potentially_ want to eliminate,
            //    iff the computation is cheap. What is cheap, though.
            // 4. Anything else.

            if inn && bpn && rcn {
                // Eliminate unused ASSIGNED
                eliminated.insert(nm.to_string());
            } else if ini && (bpi || bpn) && (rci || rcn) {
                // LOCALise if always written first
                eliminated.insert(nm.to_string());
                // ... if we consume the variable, put them into LOCAL
                if inr {
                    self.breakpoint
                        .as_mut()
                        .map(|p| p.body.data.locals.push(assign.clone()));
                }
                if bpr {
                    self.net_receive
                        .as_mut()
                        .map(|p| p.body.data.locals.push(assign.clone()));
                }
                if rcr {
                    self.initial
                        .as_mut()
                        .map(|p| p.body.data.locals.push(assign.clone()));
                }
            }
            // Treat unintialised reads
            if !ini && inr {
                return Err(ModcxxError::UninitialisedAssigned(
                    nm.to_string(),
                    "INITIAL".into(),
                ));
            }
            if !ini && !bpi && bpr {
                return Err(ModcxxError::UninitialisedAssigned(
                    nm.to_string(),
                    "BREAKPOINT".into(),
                ));
            }
            if !ini && !bpi && !rci && rcr {
                return Err(ModcxxError::UninitialisedAssigned(
                    nm.to_string(),
                    "BREAKPOINT".into(),
                ));
            }
        }
        self.assigned.retain(|var| !eliminated.contains(&var.name));
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

    pub fn eliminate_dead_locals(mut self) -> Result<Self> {
        fn eliminate_in_block(blk: &mut Block) -> Result<()> {
            let mut used = Map::new();
            for stmnt in &mut blk.stmnts {
                if let StatementT::Block(ref mut inner) = &mut stmnt.data {
                    eliminate_in_block(inner)?;
                }
                used.append(&mut stmnt.uses());
            }
            blk.locals.sort_by_key(|var| var.name.to_string());
            blk.locals.dedup_by_key(|var| var.name.to_string());
            blk.locals.retain(|var| used.contains_key(&var.name));
            Ok(())
        }

        loop {
            let mut new = self.clone();

            for proc in &mut [&mut new.breakpoint, &mut new.initial, &mut new.net_receive] {
                if let Some(ref mut blk) = proc.as_mut() {
                    eliminate_in_block(&mut blk.body)?;
                }
            }

            for procs in &mut [&mut new.kinetics, &mut new.procedures, &mut new.derivatives] {
                for proc in procs.iter_mut() {
                    eliminate_in_block(&mut proc.body)?;
                }
            }

            if new == self {
                break;
            }
            self = new;
        }
        Ok(self)
    }
}

fn inline_into_block(blk: &mut Block, procs: &Map<String, (Vec<String>, Block)>) -> Result<()> {
    let mut depth = 0;
    loop {
        let mut new = blk.clone();
        for stmnt in new.stmnts.iter_mut() {
            match stmnt.data {
                StatementT::Call(Expression {
                    data: ExpressionT::Call(ref cname, ref cargs),
                    ..
                }) => {
                    if let Some((pargs, pbody)) = procs.get(cname) {
                        let mut new = Statement::block(pbody.clone());
                        for (f, t) in pargs.iter().zip(cargs.iter()) {
                            new = new.substitute(&ExpressionT::Variable(f.to_string()), t)?
                        }
                        *stmnt = new;
                    }
                }
                StatementT::Block(ref mut blk) => inline_into_block(blk, procs)?,
                _ => {}
            }
        }
        if new == *blk {
            break;
        }
        if depth > 10 {
            unimplemented!(); // Recursion depth!
        }
        *blk = new;
        depth += 1;
    }
    Ok(())
}

fn check_duplicates_and_keywords(module: &Module) -> Result<()> {
    fn check(name: &str, loc: Location, seen: &mut Map<String, Location>) -> Result<()> {
        if let Some(old) = seen.get(name) {
            return Err(ModcxxError::DuplicateSymbol(name.to_string(), loc, *old));
        }
        if KEYWORDS.iter().find(|p| p.0 == name).is_some() {
            return Err(ModcxxError::ReservedWord(name.to_string(), loc));
        }
        seen.insert(name.to_string(), loc);
        Ok(())
    }

    let mut seen = Map::new();
    for items in &[
        &module.non_specific_currents,
        &module.assigned,
        &module.parameters,
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

fn check_scopes(module: &Module) -> Result<()> {
    fn check(
        uses: &Map<String, Vec<(Use, Location)>>,
        globals: &Map<String, Access>,
        solvables: &Set<String>,
        functions: &Map<String, usize>,
    ) -> Result<()> {
        for (var, acc) in uses {
            if let Some(n) = functions.get(var) {
                for (inv, loc) in acc {
                    match inv {
                        Use::R | Use::W => {
                            return Err(ModcxxError::CallableNotVariable(var.to_string(), *loc))
                        }
                        Use::CallF(m) | Use::CallP(m) if *n != *m => {
                            return Err(ModcxxError::WrongArity(var.to_string(), *n, *m, *loc))
                        }
                        Use::CallF(_) | Use::CallP(_) => {} // OK
                        Use::Solve => {
                            return Err(ModcxxError::CallableNotSolvable(var.to_string(), *loc))
                        }
                        Use::Unknown => {} // Maybe OK
                    }
                }
            } else if let Some(v) = globals.get(var) {
                for (inv, loc) in acc {
                    match inv {
                        Use::R => {}
                        Use::W if *v == Access::RO => {
                            return Err(ModcxxError::WriteToRO(var.to_string(), *loc))
                        }
                        Use::W => {}
                        Use::Solve => {
                            return Err(ModcxxError::CallableNotSolvable(var.to_string(), *loc))
                        }
                        Use::CallP(_) | Use::CallF(_) => {
                            return Err(ModcxxError::VariableNotCallable(var.to_string(), *loc))
                        }
                        Use::Unknown => {}
                    }
                }
            } else if solvables.contains(var) {
                for (inv, loc) in acc {
                    match inv {
                        Use::R | Use::W => {
                            return Err(ModcxxError::SolvableNotVariable(var.to_string(), *loc))
                        }
                        Use::CallP(_) | Use::CallF(_) => {
                            return Err(ModcxxError::SolvableNotCallable(var.to_string(), *loc))
                        }
                        Use::Solve => {}
                        Use::Unknown => {}
                    }
                }
            } else {
                return Err(ModcxxError::UnboundName(
                    var.to_string(),
                    acc.first().unwrap().1,
                ));
            }
        }
        Ok(())
    }

    let mut globals = Map::new();
    for g in &KNOWN {
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
    for items in &[&module.linears, &module.kinetics] {
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
            check(&item.use_timeline(), &globals, &solves, &funcs)?;
        }
    }

    for item in &[&module.breakpoint, &module.initial, &module.net_receive] {
        if let Some(f) = item {
            check(&f.use_timeline(), &globals, &solves, &funcs)?;
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
    Ok(Callable::procedure(
        &kin.name,
        &[],
        None,
        body,
        kin.loc,
    ))
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
        for op in &mut[&mut res.breakpoint,
                       &mut res.initial,
                       &mut res.net_receive] {
            if let Some(ref mut p) = op {
                *p = p.simplify()?;
            }
        }
        Ok(res)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
}
