use crate::{
    err::{ModcxxError, Result},
    exp::{
        Access, Block, Callable, Expression, ExpressionT, Statement, StatementT, Symbol, Unit, Use, Variable,
    },
    par::{self, Ion, Kind},
    Map, Set, lex::KEYWORDS, src::Location,
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
    pub functions: Vec<Callable>,
    pub constants: Vec<Symbol>,
    pub net_receive: Option<Callable>,
}

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

        let derivatives = module.derivatives.clone();
        let assigned = module.assigned.clone();
        let units = module.units.clone();
        let constants = module.constants.clone();
        let functions = module.functions.clone();
        let procedures = module.procedures.clone();
        let parameters = module.parameters.clone();
        let kinetics = module.kinetics.clone();

        let res = Module { title,
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
                           net_receive, };

        check_duplicates_and_keywords(&res)?;
        check_scopes(&res)?;

        Ok(res)
    }

    pub fn eliminate_dead_blocks(mut self) -> Result<Self> {
        // Let's figure out some data flow
        let mut used = Map::new();
        // NET_RECEIVE, INITIAL, and BREAKPOINT are our entry points
        if let Some(blk) = &self.initial {
            for (k, mut v) in blk.uses().into_iter() {
                used.entry(k).or_insert_with(Set::new).append(&mut v);
            }
        }
        if let Some(blk) = &self.breakpoint {
            for (k, mut v) in blk.uses().into_iter() {
                used.entry(k).or_insert_with(Set::new).append(&mut v);
            }
        }
        if let Some(blk) = &self.net_receive {
            for (k, mut v) in blk.uses().into_iter() {
                used.entry(k).or_insert_with(Set::new).append(&mut v);
            }
        }

        // Now recurse into procedures, functions, derivatives, and kinetics.
        loop {
            let mut new = used.clone();

            for (k, v) in &used {
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
                if v.contains(&Use::CallP) {
                    let blk = self
                        .procedures
                        .iter()
                        .find_map(|s| if &s.name == k { Some(s.uses()) } else { None })
                        .unwrap_or(Map::new());
                    for (q, mut w) in blk.into_iter() {
                        new.entry(q).or_insert_with(Set::new).append(&mut w);
                    }
                }
                if v.contains(&Use::CallF) {
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
        fn first_use_of(stmnts: &[Statement], out: &mut Map<String, Use>) {
            let mut res = Map::new();
            for other in stmnts {
                for (k, vs) in &other.uses() {
                    // NOTE: in this statement
                    //   x = x + 42
                    // we get both a READ and a WRITE, but the READ occurs
                    // first, so that's what we return.
                    for u in &[Use::R, Use::W] {
                        if vs.contains(u) {
                            res.entry(k.to_string()).or_insert(*u);
                        }
                    }
                }
            }
            for (k, v) in res.into_iter() {
                if v == Use::R {
                    // Read first disables
                    out.insert(k, v);
                } else {
                    // Write may work
                    out.entry(k).or_insert(v);
                }
            }
        }

        let mut uses = Map::new();

        if let Some(prc) = self.initial.as_ref() {
            first_use_of(&prc.body.stmnts, &mut uses)
        }
        if let Some(prc) = &self.breakpoint {
            for stmnt in &prc.body.stmnts {
                if let StatementT::Solve(nm, _) = &stmnt.data {
                    for kin in &self.kinetics {
                        if &kin.name == nm {
                            first_use_of(&kin.body.stmnts, &mut uses);
                        }
                    }
                    for blk in &self.derivatives {
                        if &blk.name == nm {
                            first_use_of(&blk.body.stmnts, &mut uses);
                        }
                    }
                }
            }
            first_use_of(&prc.body.stmnts, &mut uses);
        }
        if let Some(prc) = self.breakpoint.as_ref() {
            first_use_of(&prc.body.stmnts, &mut uses)
        }

        for assign in &self.assigned {
            // NOTE: We don't touch unused variables here, these will be
            // eliminated completely by another pass.
            if let Some(Use::W) = uses.get(&assign.name) {
                if let Some(prc) = self.initial.as_mut() {
                    prc.body.locals.push(assign.clone())
                }
                if let Some(prc) = self.breakpoint.as_mut() {
                    prc.body.locals.push(assign.clone())
                }
                if let Some(prc) = self.net_receive.as_mut() {
                    prc.body.locals.push(assign.clone())
                }
                for blk in self.derivatives.iter_mut() {
                    blk.body.locals.push(assign.clone());
                }
                for blk in self.kinetics.iter_mut() {
                    blk.body.locals.push(assign.clone());
                }
            }
        }
        self.assigned.retain(|var| {
            uses.get(&var.name)
                .as_ref()
                .map(|u| **u != Use::W)
                .unwrap_or(true)
        });
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
            return Err(ModcxxError::DuplicateSymbol(
                name.to_string(),
                loc,
                *old,
            ));
        }
        if KEYWORDS.iter().find(|p| p.0 == name).is_some() {
            return Err(ModcxxError::ReservedWord(
                name.to_string(), loc,))
        }
        seen.insert(name.to_string(), loc);
        Ok(())
    }

    let mut seen = Map::new();
    for items in &[&module.non_specific_currents,
                   &module.assigned,
                   &module.parameters,
                   &module.constants,] {
        for item in items.iter() {
            check(&item.name, item.loc, &mut seen)?;
        }
    }

    for items in &[&module.derivatives,
                   &module.kinetics,
                   &module.functions,
                   &module.procedures,] {
        for item in items.iter() {
            check(&item.name, item.loc, &mut seen)?;
        }
    }

    Ok(())
}

fn check_scopes(module: &Module) -> Result<()> {
    fn check(uses: &Map<String, Set<Use>>,
             globals: &Map<String, Access>,
             functions: &Set<String>) -> Result<()>{
        for (var, acc) in uses {
            if functions.contains(var) {
                if acc.contains(&Use::R) || acc.contains(&Use::W) {
                    return Err(ModcxxError::CallableNotVariable(var.to_string(), Location::default()));
                }
            } else if let Some(v) = globals.get(var) {
                if acc.contains(&Use::W) && *v == Access::RO {
                    return Err(ModcxxError::WriteToRO(var.to_string(), Location::default()));
                }
                if acc.contains(&Use::CallF) || acc.contains(&Use::CallP) {
                    return Err(ModcxxError::VariableNotCallable(var.to_string(), Location::default()));
                }
            } else {
                return Err(ModcxxError::UnboundName(var.to_string(), Location::default()));
            }
        }
        Ok(())
    }

    let mut globals = Map::new();
    for vars in &[&module.constants,
                   &module.parameters,
                   &module.states,
                   &module.assigned,] {
        for var in vars.iter() {
            globals.insert(var.name.to_string(), var.access);
        }
    }

    for var in &module.non_specific_currents {
        globals.insert(var.name.to_string(), var.access);
    }

    for ion in &module.ions {
        for var in &ion.vars {
            globals.insert(var.name.to_string(), var.access);
        }
    }


    let mut funcs = Set::new();
    for items in &[&module.kinetics,
                   &module.procedures,
                   &module.functions,] {
        for item in items.iter() {
            funcs.insert(item.name.to_string());
        }
    }


    for items in &[&module.derivatives,
                   &module.kinetics,
                   &module.functions,
                   &module.procedures,] {
        for item in items.iter() {
            check(&item.uses(), &globals, &funcs)?;
        }
    }

    for item in &[&module.breakpoint,
                  &module.initial,
                  &module.net_receive] {
        if let Some(f) = item {
            check(&f.uses(), &globals, &funcs)?;
        }
    }

    Ok(())
}
