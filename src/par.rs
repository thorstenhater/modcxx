use crate::err::{ModcxxError, Result};
use crate::lex::{Lexer, Token, Type};
use crate::loc::Location;
use crate::src::Code;

use crate::exp::{
    self, Block, Callable, Expression, ExpressionT, Independent, Operator, Statement, StatementT,
    Symbol, Unit, Variable,
};

use crate::Set;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Units {
    pub names: Vec<Unit>,
    pub definitions: Vec<Unit>,
}

impl Units {
    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Module {
    pub title: Vec<(String, Location)>,
    pub description: Vec<String>,
    pub neuron: Vec<Neuron>,
    pub initial: Vec<Callable>,
    pub breakpoint: Vec<Callable>,
    pub derivatives: Vec<Callable>,
    pub states: Vec<Variable>,
    pub assigned: Vec<Symbol>,
    pub parameters: Vec<Symbol>,
    pub units: Units,
    pub procedures: Vec<Callable>,
    pub kinetics: Vec<Callable>,
    pub linears: Vec<Callable>,
    pub functions: Vec<Callable>,
    pub independents: Vec<Independent>,
    pub constants: Vec<Symbol>,
    pub net_receive: Vec<Callable>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    Point,
    Density,
    ArtificialCell,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NeuronKind {
    pub kind: Kind,
    pub name: String,
    pub meta: Location,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ion {
    pub name: String,
    pub vars: Vec<Symbol>,
    pub vale: Option<Expression>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Neuron {
    pub kind: Vec<NeuronKind>,
    pub non_specific_currents: Vec<Symbol>,
    pub ions: Vec<Ion>,
    pub ranges: Vec<String>,
    pub globals: Vec<String>,
    pub pointers: Vec<(String, Location)>,
    pub location: Location,
}

pub struct Parser {
    pub lexer: Lexer,
}

impl Parser {
    pub fn new(lexer: Lexer) -> Self {
        Parser { lexer }
    }

    pub fn new_from_str(input: &str) -> Self {
        let code = Code::new(input);
        let lexer = Lexer::new(code);
        Parser::new(lexer)
    }

    /// Parse STATE block; return list of state variables
    fn states(&mut self) -> Result<Vec<Symbol>> {
        use Type::*;
        let mut res = Vec::new();
        self.expect(State)?;
        self.expect(LeftBrace)?;
        while let Some(t) = self.matches(Identifier) {
            let name = t.val.unwrap();
            let range = self.range_from_to()?;
            let start = if self.matches(Start).is_some() {
                Some(self.number()?)
            } else {
                None
            };
            let unit = self.unit()?;
            res.push(Symbol::state(&name, unit, range, start, t.loc));
        }
        self.expect(RightBrace)?;
        Ok(res)
    }

    fn range_from_to(&mut self) -> Result<Option<(String, String)>> {
        if self.matches(Type::From).is_some() {
            let lo = self.number()?;
            self.expect(Type::To)?;
            let hi = self.number()?;
            Ok(Some((lo, hi)))
        } else {
            Ok(None)
        }
    }

    /// Parse ASSIGNED block; return list of variables
    fn assigned(&mut self) -> Result<Vec<Symbol>> {
        use Type::*;
        let mut res = Vec::new();
        self.expect(Assigned)?;
        self.expect(LeftBrace)?;
        while let Some(t) = self.matches(Identifier) {
            let name = t.val.unwrap();
            let range = self.range_from_to()?;
            let unit = self.unit()?;
            res.push(Symbol::assigned(&name, unit, range, None, t.loc));
        }
        self.expect(RightBrace)?;
        Ok(res)
    }

    /// Parse PARAMETER block; return list of parameters
    fn parameters(&mut self) -> Result<Vec<Symbol>> {
        use Type::*;
        let mut res = Vec::new();
        self.expect(Parameter)?;
        self.expect(LeftBrace)?;
        while let Some(t) = self.matches(Identifier) {
            let name = t.val.unwrap();
            let start = if self.matches(Assign).is_some() {
                Some(self.number()?)
            } else {
                None
            };
            let unit = self.unit()?;
            let range = if self.matches(LT).is_some() {
                let lo = self.number()?;
                self.expect(Comma)?;
                let hi = self.number()?;
                self.expect(GT)?;
                Some((lo, hi))
            } else {
                None
            };
            res.push(Symbol::parameter(&name, unit, range, start, t.loc));
        }
        self.expect(RightBrace)?;
        Ok(res)
    }

    /// Parse UNITS block; return list of units
    fn units(&mut self) -> Result<(Units, Vec<Symbol>)> {
        use Type::*;
        self.expect(Units)?;
        self.expect(LeftBrace)?;
        let mut units = Vec::new();
        let mut defs = Vec::new();
        let mut consts = Vec::new();
        loop {
            match self.lexer.peek().typ {
                LeftParen => {
                    let lhs = self.unit()?.unwrap();
                    self.expect(Assign)?;
                    let rhs = self.unit()?.unwrap();
                    units.push(lhs);
                    defs.push(rhs);
                }
                Identifier => {
                    let id = self.expect(Identifier)?;
                    self.expect(Assign)?;
                    match self.lexer.peek().typ {
                        Number => {
                            let val = self.number()?;
                            let unit = self.unit()?;
                            consts.push(Symbol::constant(&id.val.unwrap(), &val, unit, id.loc));
                        }
                        LeftParen => {
                            let lhs = self.unit()?.unwrap();
                            let rhs = self.unit()?.unwrap();
                            units.push(lhs.clone());
                            defs.push(rhs.clone());
                            consts.push(Symbol::known(&id.val.unwrap(), Some(lhs.clone()), id.loc));
                        }
                        _ => unreachable!(),
                    }
                }
                RightBrace => {
                    break;
                }
                _ => unreachable!(),
            }
        }
        self.expect(RightBrace)?;
        Ok((
            self::Units {
                names: units,
                definitions: defs,
            },
            consts,
        ))
    }

    /// Parse INDEPENDENT blocks
    fn independent(&mut self) -> Result<Independent> {
        use Type::*;
        self.expect(Independent)?;
        self.expect(LeftBrace)?;
        let var = self.expect(Identifier)?.val.unwrap();
        self.expect(From)?;
        let from = self.number()?;
        self.expect(To)?;
        let to = self.number()?;
        self.expect(With)?;
        let with = self.number()?;
        let unit = self.unit()?;
        self.expect(RightBrace)?;
        Ok(self::Independent {
            var,
            from,
            to,
            with,
            unit,
        })
    }

    /// parse NEURON block
    fn neuron(&mut self) -> Result<Neuron> {
        use Type::*;
        self.expect(Neuron)?;
        self.expect(LeftBrace)?;
        let mut res = self::Neuron::default();
        while let Some(tok) = self.matches_one_of(&[
            Suffix,
            PointProcess,
            NonSpecificCurrent,
            Ion,
            Range,
            Global,
            Threadsafe,
            Pointer,
            BbcPointer,
            ArtificialCell,
        ]) {
            match tok.typ {
                Suffix | PointProcess | ArtificialCell => {
                    let k = match tok.typ {
                        Suffix => Kind::Density,
                        ArtificialCell => Kind::ArtificialCell,
                        PointProcess => Kind::Point,
                        _ => unreachable!(),
                    };
                    let name = self.expect(Identifier)?.val.unwrap();
                    res.kind.push(NeuronKind {
                        kind: k,
                        name,
                        meta: tok.loc,
                    });
                }
                Threadsafe => continue,
                Pointer | BbcPointer => {
                    let id = self.expect(Identifier)?;
                    res.pointers.push((id.val.unwrap(), tok.loc));
                }
                NonSpecificCurrent => res.non_specific_currents.extend(
                    self.list_of()?
                        .iter()
                        .map(|(s, l)| Symbol::global(s, *l))
                        .collect::<Vec<_>>(),
                ),
                Range => res.ranges.extend(
                    self.list_of()?
                        .iter()
                        .map(|t| t.0.to_string())
                        .collect::<Vec<_>>(),
                ),
                Global => res.globals.extend(
                    self.list_of()?
                        .iter()
                        .map(|t| t.0.to_string())
                        .collect::<Vec<_>>(),
                ),
                Ion => res.ions.push(self.ion()?),
                _ => unreachable!(),
            }
        }
        self.expect(RightBrace)?;
        Ok(res)
    }

    fn skip(&mut self) {
        self.lexer.advance();
    }

    fn expect(&mut self, typ: Type) -> Result<Token> {
        self.expect_one_of(&[typ])
    }

    fn expect_one_of(&mut self, types: &[Type]) -> Result<Token> {
        if let Some(tok) = self.matches_one_of(types) {
            Ok(tok)
        } else {
            self.lexer.code.mark_location(&self.lexer.peek().loc);
            Err(self.unexpected_token(types))
        }
    }

    fn list_of(&mut self) -> Result<Vec<(String, Location)>> {
        let mut res = Vec::new();
        if let Some(tok) = self.matches(Type::Identifier) {
            res.push((tok.val.unwrap(), tok.loc));
            while self.matches(Type::Comma).is_some() {
                let tok = self.expect(Type::Identifier)?;
                res.push((tok.val.unwrap(), tok.loc));
            }
        }
        Ok(res)
    }

    fn matches_one_of(&mut self, types: &[Type]) -> Option<Token> {
        let typ = self.lexer.peek().typ;
        if types.contains(&typ) {
            Some(self.lexer.advance())
        } else {
            None
        }
    }

    fn matches(&mut self, typ: Type) -> Option<Token> {
        self.matches_one_of(&[typ])
    }

    fn ion(&mut self) -> Result<Ion> {
        use Type::*;
        let nm = self.expect(Identifier)?.val.unwrap();
        let rs = if self.matches(Read).is_some() {
            self.list_of()?
        } else {
            Vec::new()
        };
        let ws = if self.matches(Write).is_some() {
            self.list_of()?
        } else {
            Vec::new()
        };
        let q = if self.matches(Valence).is_some() {
            Some(self.expression()?)
        } else {
            None
        };
        // Do some initial validation
        let mut symbols = Vec::new();
        let mut seen = Set::new();
        for (sym, loc) in ws {
            if sym.starts_with(&nm) || sym.ends_with(&nm) {
                symbols.push(Symbol::global(&sym, loc));
                seen.insert(sym);
            } else {
                return Err(ModcxxError::IllegalIonic(loc, sym, nm));
            }
        }
        for (sym, loc) in rs {
            if sym.starts_with(&nm) || sym.ends_with(&nm) {
                if !seen.contains(&sym) {
                    symbols.push(Symbol::readonly(&sym, loc));
                    seen.insert(sym);
                }
            } else {
                return Err(ModcxxError::IllegalIonic(loc, sym, nm));
            }
        }
        Ok(self::Ion {
            name: nm,
            vars: symbols,
            vale: q,
        })
    }

    pub fn module(&mut self) -> Result<Module> {
        use Type::*;
        let mut result = Module::default();
        while self.lexer.peek().typ != EOF {
            let tok = self.lexer.peek();
            match tok.typ {
                Title => {
                    let title = self.expect(Title)?;
                    result.title.push((title.val.unwrap(), title.loc));
                    // NOTE only Title into comment qualifies... maybe? heuristic
                    if self.lexer.peek().typ == Comment {
                        result.description.push(self.expect(Comment)?.val.unwrap());
                    }
                }
                Comment => self.skip(),
                Neuron => result.neuron.push(self.neuron()?),
                Include => {
                    let tok = self.expect(Include)?;
                    return Err(ModcxxError::Unsupported(
                        "INCLUDE".into(),
                        self.lexer.code.mark_location(&tok.loc),
                    ));
                }
                Verbatim => {
                    let tok = self.expect(Verbatim)?;
                    return Err(ModcxxError::Unsupported(
                        "VERBATIM".into(),
                        self.lexer.code.mark_location(&tok.loc),
                    ));
                }
                Initial => result.initial.push(self.initial()?),
                Kinetic => result.kinetics.push(self.kinetic()?),
                Linear => result.linears.push(self.linear()?),
                Constant => result.constants.append(&mut self.constants()?),
                Destructor => {
                    let tok = self.expect(Destructor)?;
                    return Err(ModcxxError::Unsupported(
                        "DESTRUCTOR".into(),
                        self.lexer.code.mark_location(&tok.loc),
                    ));
                }
                Breakpoint => result.breakpoint.push(self.breakpoint()?),
                NetReceive => result.net_receive.push(self.net_receive()?),
                // NOTE: Top level LOCAL means ASSIGNED? Maybe... man this is crazy
                Local => result.assigned.append(&mut self.locals()?),
                Independent => result.independents.push(self.independent()?),
                Derivative => result.derivatives.push(self.derivative()?),
                Procedure => result.procedures.push(self.procedure()?),
                Function => result.functions.push(self.function()?),
                Assigned => result.assigned.extend(self.assigned()?),
                State => result.states.extend(self.states()?),
                Units => {
                    let (mut units, mut consts) = self.units()?;
                    result.units.names.append(&mut units.names);
                    result.units.definitions.append(&mut units.definitions);
                    result.constants.append(&mut consts);
                }
                Parameter => result.parameters.extend(self.parameters()?),
                UnitsOn | UnitsOff => self.skip(),
                _ => {
                    return Err(self.unexpected_token(&[
                        Neuron, State, Parameter, Assigned, Initial, Breakpoint, Title, Comment,
                        Units,
                    ]))
                }
            }
        }
        Ok(result)
    }

    fn unexpected_token(&self, tys: &[Type]) -> ModcxxError {
        let tok = self.lexer.peek();
        ModcxxError::UnexpectedToken(tok.loc, tok.typ, tok.val, tys.to_vec())
    }

    fn number(&mut self) -> Result<String> {
        let mut res = String::new();
        if self.matches(Type::Sub).is_some() {
            res.push('-');
        }
        res += &self.expect(Type::Number)?.val.unwrap();
        self.unit()?;
        Ok(res)
    }

    fn initial(&mut self) -> Result<Callable> {
        let init = self.expect(Type::Initial)?;
        let body = self.block()?;
        Ok(Callable::initial(body, init.loc))
    }

    fn kinetic(&mut self) -> Result<Callable> {
        let ds = self.expect(Type::Kinetic)?;
        let id = self.expect(Type::Identifier)?;
        let body = self.block()?;
        Ok(Callable::kinetic(&id.val.unwrap(), body, ds.loc))
    }

    fn linear(&mut self) -> Result<Callable> {
        let ds = self.expect(Type::Linear)?;
        let id = self.expect(Type::Identifier)?;
        let body = self.block()?;
        Ok(Callable::linear(&id.val.unwrap(), body, ds.loc))
    }

    pub fn derivative(&mut self) -> Result<Callable> {
        let ds = self.expect(Type::Derivative)?;
        let id = self.expect(Type::Identifier)?;
        let body = self.block()?;
        Ok(Callable::derivative(&id.val.unwrap(), body, ds.loc))
    }

    fn procedure(&mut self) -> Result<Callable> {
        let proc = self.expect(Type::Procedure)?;
        let id = self.expect(Type::Identifier)?;
        let args = self.formals()?;
        let unit = self.unit()?;
        let body = self.block()?;
        Ok(Callable::procedure(
            &id.val.unwrap(),
            &args,
            unit,
            body,
            proc.loc,
        ))
    }

    fn net_receive(&mut self) -> Result<Callable> {
        let proc = self.expect(Type::NetReceive)?;
        let args = self.formals()?;
        let unit = self.unit()?;
        let body = self.block()?;
        Ok(Callable::procedure(
            "NET_RECEIVE",
            &args,
            unit,
            body,
            proc.loc,
        ))
    }

    fn function(&mut self) -> Result<Callable> {
        let proc = self.expect(Type::Function)?;
        let id = self.expect(Type::Identifier)?;
        let args = self.formals()?;
        let unit = self.unit()?;
        let mut body = self.block()?;

        // We patch
        //
        //   FUNCTION foo() { foo = 42 }
        //
        // into
        //
        //   FUNCTION foo() { return 42 }
        fn patch_stmnt(stmnt: &mut Statement, name: &str) {
            match &mut stmnt.data {
                StatementT::Assign(lhs, rhs) if lhs == name => {
                    stmnt.data = StatementT::Return(rhs.clone());
                }
                StatementT::IfThenElse(_, t, e) => {
                    patch_block(t, name);
                    if let Some(ref mut e) = e {
                        patch_block(e, name);
                    }
                }
                StatementT::Block(ref mut blk) => patch_block(blk, name),
                _ => {}
            }
        }
        fn patch_block(block: &mut Block, name: &str) {
            for stmnt in block.stmnts.iter_mut() {
                patch_stmnt(stmnt, name);
            }
        }
        let name = &id.val.unwrap();
        patch_block(&mut body, name);
        Ok(Callable::function(name, args, unit, body, proc.loc))
    }

    fn formals(&mut self) -> Result<Vec<Symbol>> {
        use Type::*;
        self.expect(LeftParen)?;
        let mut args = Vec::new();
        if let Some(id) = self.matches(Identifier) {
            let unit = self.unit()?;
            args.push(Symbol::argument(&id.val.unwrap(), unit, id.loc));
        }
        while self.matches(RightParen).is_none() {
            self.expect(Comma)?;
            let id = self.expect(Identifier)?;
            let unit = self.unit()?;
            args.push(Symbol::argument(&id.val.unwrap(), unit, id.loc));
        }
        Ok(args)
    }

    fn solve(&mut self) -> Result<Statement> {
        use Type::*;
        let loc = self.expect(Solve)?.loc;
        let blk = self.expect(Identifier)?;
        let res = match self.matches_one_of(&[Method, SteadyState]).map(|t| t.typ) {
            Some(Method) => exp::Statement::solve(
                &blk.val.unwrap(),
                &self.expect(Identifier)?.val.unwrap(),
                loc,
            ),
            Some(SteadyState) => exp::Statement::steadystate(
                &blk.val.unwrap(),
                &self.expect(Identifier)?.val.unwrap(),
                loc,
            ),
            None => exp::Statement::solve_default(&blk.val.unwrap(), loc),
            _ => unreachable!(),
        };
        Ok(res)
    }

    fn breakpoint(&mut self) -> Result<Callable> {
        let blk = self.expect(Type::Breakpoint)?;
        let body = self.block()?;
        Ok(Callable::breakpoint(body, blk.loc))
    }

    pub fn block(&mut self) -> Result<Block> {
        use Type::*;
        let beg = self.expect(LeftBrace)?.loc;
        let mut locals = self.locals()?;
        let mut stmnts = Vec::new();
        loop {
            let tok = self.lexer.peek();
            match tok.typ {
                RightBrace => break,
                UnitsOn | UnitsOff => {
                    self.skip();
                    continue;
                }
                Table => {
                    self.skip();
                    self.list_of()?;
                    if self.matches(Depend).is_some() {
                        self.list_of()?;
                    }
                    while self.matches_one_of(&[From, To, With]).is_some() {
                        if self.lexer.peek().typ == Identifier {
                            self.skip();
                        } else {
                            self.number()?;
                        }
                    }
                }
                Local => {
                    // TODO this is a hack and messes up scoping by allowing
                    // variables beeing named before introduction.
                    locals.append(&mut self.locals()?);
                }
                Verbatim => {
                    return Err(ModcxxError::Unsupported(
                        "VERBATIM".into(),
                        self.lexer.code.mark_location(&tok.loc),
                    ));
                }
                _ => stmnts.push(self.statement()?),
            }
        }
        self.expect(RightBrace)?;
        Ok(Block::block(&locals, &stmnts, beg))
    }

    fn locals(&mut self) -> Result<Vec<Variable>> {
        if self.matches(Type::Local).is_some() {
            Ok(self
                .list_of()?
                .iter()
                .map(|(s, l)| Variable::local(s, *l))
                .collect())
        } else {
            Ok(Vec::new())
        }
    }

    pub fn statement(&mut self) -> Result<Statement> {
        use Type::*;
        match self.lexer.peek().typ {
            Solve => self.solve(),
            If => {
                let loc = self.expect(If)?.loc;
                self.expect(LeftParen)?;
                let cond = self.expression()?;
                self.expect(RightParen)?;
                let then = self.block()?;
                let neht = if self.matches(Else).is_some() {
                    if self.lexer.peek().typ == If {
                        let nested = self.statement()?;
                        let loc = nested.loc;
                        Some(Block::block(&[], &[nested], loc))
                    } else {
                        Some(self.block()?)
                    }
                } else {
                    None
                };
                Ok(Statement::if_then_else(cond, then, neht, loc))
            }
            Identifier => {
                let id = self.expect(Identifier)?;
                match self.lexer.peek().typ {
                    Assign => {
                        let loc = self.expect(Assign)?.loc;
                        let rhs = self.expression()?;
                        Ok(Statement::assign(&id.val.unwrap(), rhs, loc))
                    }
                    Prime => {
                        let _ = self.expect(Prime)?;
                        let loc = self.expect(Assign)?.loc;
                        let rhs = self.expression()?;
                        Ok(Statement::derivative(&id.val.unwrap(), rhs, loc))
                    }
                    LeftParen => {
                        let args = self.arguments()?;
                        Ok(Statement::call(&id.val.unwrap(), args, id.loc))
                    }
                    _ => Err(self.unexpected_token(&[Assign, LeftParen])),
                }
            }
            Conserve => {
                let loc = self.expect(Conserve)?.loc;
                let lhs = self.expression()?;
                self.expect(Assign)?;
                let rhs = self.expression()?;
                Ok(Statement::conserve(lhs, rhs, loc))
            }
            Tilde => {
                let loc = self.expect(Tilde)?.loc;
                let from = self.expression()?;
                match self.lexer.peek().typ {
                    LRArrow => {
                        self.expect(LRArrow)?;
                        // Nasty: If the next bit is foo (a, b) we parse it erroneously
                        // as a call...
                        let rest = self.expression()?;
                        if self.lexer.peek().typ == LeftParen {
                            // We did not fall for this trap... so our `to` is `rest`
                            self.expect(LeftParen)?;
                            let fwd = self.expression()?;
                            self.expect(Comma)?;
                            let bwd = self.expression()?;
                            self.expect(RightParen)?;
                            Ok(Statement::rate(from, rest, fwd, bwd, loc))
                        } else {
                            // We did fall for it... Oh my, now we take `rest` apart...
                            if let ExpressionT::Call(nm, args) = rest.data {
                                let to = Expression::variable(&nm, rest.loc);
                                if let [fwd, bwd] = &args[..] {
                                    Ok(Statement::rate(from, to, fwd.clone(), bwd.clone(), loc))
                                } else {
                                    panic!()
                                }
                            } else {
                                panic!()
                            }
                        }
                    }
                    Assign => {
                        self.expect(Assign)?;
                        let rhs = self.expression()?;
                        Ok(Statement::linear(from, rhs, loc))
                    }
                    _ => Err(self.unexpected_token(&[LRArrow, Eq])),
                }
            }
            Initial => {
                let loc = self.expect(Initial)?.loc;
                let blk = self.block()?;
                Ok(Statement::initial(blk, loc))
            }
            LeftBrace => Ok(Statement::block(self.block()?)),
            _ => Err(self.unexpected_token(&[If, Identifier, LeftBrace, Tilde])),
        }
    }

    pub fn expression(&mut self) -> Result<Expression> {
        self.logical()
    }

    fn binary(
        &mut self,
        types: &[Type],
        ops: &[Operator],
        next: &mut dyn FnMut(&mut Self) -> Result<Expression>,
    ) -> Result<Expression> {
        let mut lhs = next(self)?;
        while let Some(tok) = self.matches_one_of(types) {
            let op = types.iter().zip(ops).find(|p| *p.0 == tok.typ).unwrap().1;
            lhs = Expression::binary(lhs, *op, next(self)?, tok.loc);
        }
        Ok(lhs)
    }

    fn logical(&mut self) -> Result<Expression> {
        self.binary(
            &[Type::And, Type::Or],
            &[Operator::And, Operator::Or],
            &mut |par: &mut Self| par.equality(),
        )
    }

    fn equality(&mut self) -> Result<Expression> {
        self.binary(
            &[Type::Eq, Type::NEq],
            &[Operator::Eq, Operator::NEq],
            &mut |par: &mut Self| par.comparison(),
        )
    }

    fn comparison(&mut self) -> Result<Expression> {
        self.binary(
            &[Type::LT, Type::LE, Type::GE, Type::GT],
            &[Operator::LT, Operator::LE, Operator::GE, Operator::GT],
            &mut |par: &mut Self| par.term(),
        )
    }

    fn term(&mut self) -> Result<Expression> {
        self.binary(
            &[Type::Add, Type::Sub],
            &[Operator::Add, Operator::Sub],
            &mut |par: &mut Self| par.factor(),
        )
    }

    fn factor(&mut self) -> Result<Expression> {
        self.binary(
            &[Type::Mul, Type::Div],
            &[Operator::Mul, Operator::Div],
            &mut |par: &mut Self| par.unary(),
        )
    }

    fn unary(&mut self) -> Result<Expression> {
        if let Some(tok) = self.matches_one_of(&[Type::Not, Type::Sub]) {
            let rhs = self.unary()?;
            let op = match tok.typ {
                Type::Not => Operator::Not,
                Type::Sub => Operator::Neg,
                _ => unreachable!(),
            };
            Ok(Expression::unary(op, rhs, tok.loc))
        } else {
            self.power()
        }
    }

    fn power(&mut self) -> Result<Expression> {
        let mut lhs = self.primary()?;
        while let Some(tok) = self.matches(Type::Pow) {
            lhs = Expression::binary(lhs, Operator::Pow, self.unary()?, tok.loc);
        }
        Ok(lhs)
    }

    fn primary(&mut self) -> Result<Expression> {
        use Type::*;
        match self.lexer.peek().typ {
            LeftParen => {
                self.expect(LeftParen)?;
                let res = self.expression();
                self.expect(RightParen)?;
                res
            }
            String => {
                let tok = self.expect(String)?;
                self.unit()?;
                Ok(Expression::string(&tok.val.unwrap(), tok.loc))
            }
            Number => {
                let tok = self.expect(Number)?;
                self.unit()?;
                Ok(Expression::number(&tok.val.unwrap(), tok.loc))
            }
            Identifier => {
                let tok = self.expect(Identifier)?;
                let exp = if self.lexer.peek().typ == LeftParen {
                    Expression::call(&tok.val.unwrap(), self.arguments()?, tok.loc)
                } else {
                    Expression::variable(&tok.val.unwrap(), tok.loc)
                };
                Ok(exp)
            }
            _ => Err(self.unexpected_token(&[LeftParen, Number, Identifier, String])),
        }
    }

    fn arguments(&mut self) -> Result<Vec<Expression>> {
        use Type::*;
        self.expect(LeftParen)?;
        let mut args = Vec::new();
        if self.lexer.peek().typ != RightParen {
            loop {
                args.push(self.expression()?);
                if self.lexer.peek().typ == RightParen {
                    break;
                }
                self.expect(Comma)?;
            }
        }
        self.expect(RightParen)?;
        Ok(args)
    }

    fn constants(&mut self) -> Result<Vec<Symbol>> {
        use Type::*;
        self.expect(Constant)?;
        self.expect(LeftBrace)?;
        let mut res = Vec::new();
        while self.lexer.peek().typ != RightBrace {
            res.push(self.constant()?);
        }
        self.expect(RightBrace)?;
        Ok(res)
    }

    fn constant(&mut self) -> Result<Symbol> {
        use Type::*;
        let id = self.expect(Identifier)?;
        self.expect(Assign)?;
        let val = self.expect(Number)?;
        let unit = self.unit()?;
        Ok(Symbol::constant(
            &id.val.unwrap(),
            &val.val.unwrap(),
            unit,
            id.loc,
        ))
    }

    // Unit parsing
    /// parse a unit declaration;
    fn unit(&mut self) -> Result<Option<Unit>> {
        use Type::*;
        if self.matches(LeftParen).is_some() {
            if self.lexer.peek().typ == RightParen {
                self.expect(RightParen)?;
                Ok(None)
            } else {
                let res = self.unit_factor()?;
                self.expect(RightParen)?;
                Ok(Some(res))
            }
        } else {
            Ok(None)
        }
    }

    fn unit_factor(&mut self) -> Result<Expression> {
        let mut lhs = self.unit_unary()?;
        use Type::*;
        loop {
            let tok = self.lexer.peek();
            match tok.typ {
                Sub => {
                    // NOTE 'Sub' here is interpreted as a hyphen. So: (kilo-Volt) = (10000 V)
                    // Amazing, no?
                    self.expect(Sub)?;
                    lhs = Expression::binary(lhs, Operator::Sub, self.unit_unary()?, tok.loc)
                }
                Mul => {
                    self.expect(Mul)?;
                    lhs = Expression::binary(lhs, Operator::Mul, self.unit_unary()?, tok.loc)
                }
                Div => {
                    self.expect(Div)?;
                    lhs = Expression::binary(lhs, Operator::Div, self.unit_unary()?, tok.loc)
                }
                Identifier => {
                    lhs = Expression::binary(lhs, Operator::Mul, self.unit_unary()?, tok.loc)
                }
                _ => break,
            }
        }
        Ok(lhs)
    }

    fn unit_unary(&mut self) -> Result<Expression> {
        if let Some(tok) = self.matches_one_of(&[Type::Div, Type::Sub]) {
            let op = match tok.typ {
                Type::Div => Operator::Div,
                Type::Sub => Operator::Neg,
                _ => unreachable!(),
            };
            Ok(Expression::unary(op, self.unit_unary()?, tok.loc))
        } else {
            self.unit_power()
        }
    }

    fn unit_power(&mut self) -> Result<Expression> {
        let mut lhs = self.unit_primary()?;
        while let Some(tok) = self.matches(Type::Pow) {
            lhs = Expression::binary(lhs, Operator::Pow, self.unit_unary()?, tok.loc);
        }
        Ok(lhs)
    }

    fn unit_primary(&mut self) -> Result<Expression> {
        use Type::*;
        match self.lexer.peek().typ {
            Number => {
                let tok = self.expect(Number)?;
                Ok(Expression::number(&tok.val.unwrap(), tok.loc))
            }
            Identifier => {
                let tok = self.expect(Identifier)?;
                Ok(Expression::variable(&tok.val.unwrap(), tok.loc))
            }
            _ => Err(self.unexpected_token(&[Number, Identifier])),
        }
    }
}

pub fn parse(input: &str) -> Result<Module> {
    Parser::new_from_str(input).module()
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::loc::Location;
    use pretty_assertions::assert_eq;

    #[test]
    fn fabs() {
        assert_eq!(
            Parser::new_from_str("fabs(x)").expression().unwrap(),
            Expression::call(
                "fabs",
                vec![Expression::variable(
                    "x",
                    Location {
                        line: 0,
                        column: 5,
                        position: 5
                    }
                )],
                Location {
                    line: 0,
                    column: 0,
                    position: 0
                }
            )
        );

        println!(
            "{:?}",
            Parser::new_from_str("fabs(-x)^2").expression().unwrap()
        );

        assert_eq!(
            Parser::new_from_str("fabs(-x)^2").expression().unwrap(),
            Expression::pow(
                Expression::call(
                    "fabs",
                    vec![Expression::neg(
                        Expression::variable(
                            "x",
                            Location {
                                line: 0,
                                column: 6,
                                position: 6
                            }
                        ),
                        Location {
                            line: 0,
                            column: 5,
                            position: 5
                        },
                    )],
                    Location {
                        line: 0,
                        column: 0,
                        position: 0
                    }
                ),
                Expression::float(
                    2,
                    Location {
                        line: 0,
                        column: 9,
                        position: 9
                    }
                ),
                Location {
                    line: 0,
                    column: 8,
                    position: 8
                }
            )
        );

        // println!(
        // "{:?}",
        // Parser::new_from_str(
        // .statement()
        // .unwrap()
        // ));

        assert_eq!(
            Parser::new_from_str("fabs(x)").expression().unwrap(),
            Expression::call(
                "fabs",
                vec![Expression::variable(
                    "x",
                    Location {
                        line: 0,
                        column: 5,
                        position: 5
                    }
                )],
                Location {
                    line: 0,
                    column: 0,
                    position: 0
                },
            )
        );

        // assert_eq!(Parser::new_from_str("if (fabs(x / y) < 1e-6) {}").statement().unwrap(),
        // Statement::if_then(Expression::call("fabs",
        // vec![Expression::variable("x", Location { line: 0, column: 5, position: 5 })],
        // Location { line: 0, column: 0, position: 0 }),

        // ));
    }

    #[test]
    fn nrn1() {
        fn check(m: &str, line: usize, column: usize, position: usize) {
            let m = parse(m).unwrap();
            let n = m.neuron.first().unwrap();
            assert_eq!(
                n.kind,
                vec![NeuronKind {
                    kind: Kind::Density,
                    name: "NaV".into(),
                    meta: Location {
                        line,
                        column,
                        position
                    }
                }]
            );
            assert_eq!(n.non_specific_currents, vec![]);
            assert_eq!(n.ions[0].name, "na");
            let ion = &n.ions[0].vars;
            let ina = &ion.iter().find(|s| s.name == "ina").unwrap().data;
            let ena = &ion.iter().find(|s| s.name == "ena").unwrap().data;
            assert_eq!(ina, &Symbol::global("ina", Location::default()).data);
            assert_eq!(ena, &Symbol::readonly("ena", Location::default()).data);
            assert_eq!(n.ranges, vec![String::from("gbar")]);
        }
        check(
            "NEURON {
  SUFFIX NaV
  RANGE gbar
  USEION na READ ena WRITE ina
}",
            1,
            2,
            11,
        );
        check(
            "NEURON {   RANGE gbar  SUFFIX NaV
  USEION na READ ena WRITE ina
}",
            0,
            23,
            23,
        );
        check(
            "NEURON{RANGE gbar SUFFIX NaV USEION na READ ena WRITE ina}",
            0,
            18,
            18,
        );
        check(
            "

NEURON{RANGE
 gbar SUFFIX NaV USEION
na READ
 ena
 WRITE
 ina}",
            3,
            6,
            21,
        );
    }

    #[test]
    fn nrn2() {
        let exp = vec![Ion {
            name: String::from("na"),
            vars: vec![],
            vale: Some(Expression::unary(
                Operator::Neg,
                Expression::number(
                    "42",
                    Location {
                        line: 0,
                        column: 40,
                        position: 40,
                    },
                ),
                Location {
                    line: 0,
                    column: 39,
                    position: 39,
                },
            )),
        }];
        assert_eq!(
            parse("NEURON{SUFFIX foobar USEION na VALENCE -42}")
                .unwrap()
                .neuron
                .first()
                .unwrap()
                .ions,
            exp
        );
        let exp = vec![Ion {
            name: String::from("na"),
            vars: vec![],
            vale: Some(Expression::unary(
                Operator::Neg,
                Expression::number(
                    "42",
                    Location {
                        line: 0,
                        column: 44,
                        position: 44,
                    },
                ),
                Location {
                    line: 0,
                    column: 39,
                    position: 39,
                },
            )),
        }];
        assert_eq!(
            parse("NEURON{SUFFIX foobar USEION na VALENCE -    42}")
                .unwrap()
                .neuron
                .first()
                .unwrap()
                .ions,
            exp
        );
    }

    #[test]
    fn stt1() {
        parse(
            "STATE {
A FROM 42 TO 23
}",
        )
        .unwrap();
        parse(
            "STATE {
A FROM 0 TO 1 (ms^-1)
}",
        )
        .unwrap();
        parse(
            "STATE {
A(ms^-1)
}",
        )
        .unwrap();
        parse(
            "STATE {
A
 (ms^-1)
}",
        )
        .unwrap();
        parse(
            "STATE {
A FROM
0
TO 42
 (ms^
-1) B FROM 1 TO -1
}",
        )
        .unwrap();
    }

    #[test]
    fn prm1() {
        parse("PARAMETER { gbar }").unwrap();
        parse("PARAMETER { gbar = 42e-4 } : Hay").unwrap();
        parse(
            "PARAMETER { gbar = 42e-4 : my g
qt (/K) <0,1000>
 } : Hay",
        )
        .unwrap();
        parse(
            "PARAMETER { gbar = 42e-4 : my g
qt =
273.15 (K) <0,1000>
 } : Hay",
        )
        .unwrap();
        parse(
            "PARAMETER { gbar = 42e-4 : my g
qt =
.15 (K) <0,1000>
 } : Cooold",
        )
        .unwrap();
    }

    #[test]
    fn mod1() {
        parse(
            "NEURON {
    SUFFIX pas
    NONSPECIFIC_CURRENT i
    RANGE g
    GLOBAL e
}

UNITS {
    (mV) = (millivolt)
    (S) = (siemens)
}

INITIAL {
  LOCAL x, y
  x = x + 42
    y= x^--5
}

PARAMETER {
    g = .001 (S/cm2)
    e = -70  (mV) : Taken from nrn
}

BREAKPOINT {
    i = g*(v - e)
}
",
        )
        .unwrap();
        parse(
            "NEURON {
    SUFFIX pas
    NONSPECIFIC_CURRENT i
    RANGE g
    :GLOBAL e
}

UNITS {
    (mV) = (millivolt)
    (S) = (siemens)
}

ASSIGNED { i FROM 0 TO 1 }

STATE {
    k FROM 0 TO 1 START 0 (me)
}

INITIAL {
  LOCAL x
  x = x + 42
  {
    LOCAL y
    y= x^--5
  }
}

PARAMETER {
    v
    g = .001 (S/cm2)
    e = -70  (mV) : Taken from nrn
}

BREAKPOINT {
    i = g*(v - e)
}
",
        )
        .unwrap();
    }

    #[test]
    fn basic() {
        assert_eq!(
            Parser::new_from_str("--42").expression().unwrap(),
            Expression::neg(
                Expression::neg(
                    Expression::number("42", Location::new(0, 2, 2)),
                    Location::new(0, 1, 1)
                ),
                Location::new(0, 0, 0)
            )
        );
        assert_eq!(
            Parser::new_from_str("!-(--(42))").expression().unwrap(),
            Expression::not(
                Expression::neg(
                    Expression::neg(
                        Expression::neg(
                            Expression::number("42", Location::new(0, 6, 6)),
                            Location::new(0, 4, 4)
                        ),
                        Location::new(0, 3, 3)
                    ),
                    Location::new(0, 1, 1)
                ),
                Location::new(0, 0, 0)
            )
        );

        Parser::new_from_str("--x*42/23").expression().unwrap();
        Parser::new_from_str("y--x*42/23").expression().unwrap();
        Parser::new_from_str("y*z--x*42").expression().unwrap();
        Parser::new_from_str("-x^-y*z").expression().unwrap();
        Parser::new_from_str("sin(x)^2").expression().unwrap();
        Parser::new_from_str("0 && 1 == 0 >= sin(x)^2")
            .expression()
            .unwrap();
    }

    #[test]
    fn precedence() {
        let exp = Parser::new_from_str("1/2/3").expression().unwrap();
        assert_eq!(
            exp,
            Expression::div(
                Expression::div(
                    Expression::number("1", Location::new(0, 0, 0)),
                    Expression::number("2", Location::new(0, 2, 2)),
                    Location::new(0, 1, 1)
                ),
                Expression::number("3", Location::new(0, 4, 4)),
                Location::new(0, 3, 3)
            )
        );

        let exp = Parser::new_from_str("-X^2").expression().unwrap();
        assert_eq!(
            exp,
            Expression::neg(
                Expression::pow(
                    Expression::variable("X", Location::new(0, 1, 1)),
                    Expression::number("2", Location::new(0, 3, 3)),
                    Location::new(0, 2, 2)
                ),
                Location::new(0, 0, 0)
            )
        );

        let exp = Parser::new_from_str("1/(2/3)").expression().unwrap();
        assert_eq!(
            exp,
            Expression::div(
                Expression::number("1", Location::new(0, 0, 0)),
                Expression::div(
                    Expression::number("2", Location::new(0, 3, 3)),
                    Expression::number("3", Location::new(0, 5, 5)),
                    Location::new(0, 4, 4)
                ),
                Location::new(0, 1, 1)
            )
        );
        let exp = Parser::new_from_str("1-2-3").expression().unwrap();
        assert_eq!(
            exp,
            Expression::sub(
                Expression::sub(
                    Expression::number("1", Location::new(0, 0, 0)),
                    Expression::number("2", Location::new(0, 2, 2)),
                    Location::new(0, 1, 1)
                ),
                Expression::number("3", Location::new(0, 4, 4)),
                Location::new(0, 3, 3)
            )
        );

        let exp = Parser::new_from_str("1-(2-3)").expression().unwrap();
        assert_eq!(
            exp,
            Expression::sub(
                Expression::number("1", Location::new(0, 0, 0)),
                Expression::sub(
                    Expression::number("2", Location::new(0, 3, 3)),
                    Expression::number("3", Location::new(0, 5, 5)),
                    Location::new(0, 4, 4)
                ),
                Location::new(0, 1, 1)
            )
        );
        let exp = Parser::new_from_str("2^3^4").expression().unwrap();
        assert_eq!(
            exp,
            Expression::pow(
                Expression::number("2", Location::new(0, 0, 0)),
                Expression::pow(
                    Expression::number("3", Location::new(0, 2, 2)),
                    Expression::number("4", Location::new(0, 4, 4)),
                    Location::new(0, 3, 3)
                ),
                Location::new(0, 1, 1)
            )
        );
    }

    #[test]
    fn statements() {
        assert_eq!(
            Parser::new_from_str("m' = 42").statement().unwrap(),
            Statement::derivative(
                "m",
                Expression::number("42", Location::new(0, 5, 5)),
                Location::new(0, 3, 3)
            )
        );
        assert_eq!(
            Parser::new_from_str("m = 42").statement().unwrap(),
            Statement::assign(
                "m",
                Expression::number("42", Location::new(0, 4, 4)),
                Location::new(0, 2, 2)
            )
        );
        assert_eq!(
            Parser::new_from_str("m' = foo").statement().unwrap(),
            Statement::derivative(
                "m",
                Expression::variable("foo", Location::new(0, 5, 5)),
                Location::new(0, 3, 3)
            )
        );
        assert_eq!(
            Parser::new_from_str("m = foo").statement().unwrap(),
            Statement::assign(
                "m",
                Expression::variable("foo", Location::new(0, 4, 4)),
                Location::new(0, 2, 2)
            )
        );
    }

    #[test]
    fn cond() {
        println!(
            "{:?}",
            Parser::new_from_str(
                "if (x) {
 y = 42
}"
            )
            .statement()
            .unwrap()
        );
        println!(
            "{:?}",
            Parser::new_from_str(
                "if (((x) )   ) {
 y = 42
}"
            )
            .statement()
            .unwrap()
        );
    }
}
