use crate::{
    err::{ModcxxError, Result},
    Map,
};
use std::{fmt::Display, sync::atomic::AtomicUsize};

// Nomrmal Variables.
pub type Var = String;
// Continuation Variables. Live in a different Environment
pub type CVar = String;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ML {
    Real(String),
    Bool(bool),
    Unit,
    Fun {
        name: Var,
        args: Vec<Var>,
        body: Box<ML>,
        rest: Box<ML>,
    },
    App {
        fun: Box<ML>,
        args: Vec<ML>,
    },
    IfThenElse {
        cond: Box<ML>,
        then: Box<ML>,
        or: Option<Box<ML>>,
    },
    Let {
        name: Var,
        value: Box<ML>,
        body: Box<ML>,
    },
    Set {
        name: Var,
        value: Box<ML>,
    },
    Var(Var),
    Seq(Vec<ML>),
}

impl ML {
    pub fn var<V>(v: V) -> Self
    where
        Var: From<V>,
    {
        Self::Var(Var::from(v))
    }

    pub fn real<V>(v: V) -> Self
    where
        String: From<V>,
    {
        Self::Real(Var::from(v))
    }

    pub fn nil() -> Self {
        Self::Unit
    }

    pub fn bool(b: bool) -> Self {
        Self::Bool(b)
    }

    pub fn set<V>(n: V, v: ML) -> Self
    where
        Var: From<V>,
    {
        Self::Set {
            name: n.into(),
            value: Box::new(v),
        }
    }

    pub fn val<V>(n: V, v: ML, b: ML) -> Self
    where
        Var: From<V>,
    {
        Self::Let {
            name: n.into(),
            value: Box::new(v),
            body: Box::new(b),
        }
    }

    pub fn seq(s: &[ML]) -> Self {
        assert!(!s.is_empty());
        Self::Seq(s.to_vec())
    }

    pub fn fun<N, V>(name: N, args: &[V], body: ML, rest: ML) -> Self
    where
        Var: From<V>,
        String: From<N>,
        V: Clone,
    {
        Self::Fun {
            name: String::from(name),
            args: args.iter().cloned().map(|x| Var::from(x)).collect(),
            body: Box::new(body),
            rest: Box::new(rest),
        }
    }

    pub fn app(n: ML, a: &[ML]) -> Self {
        Self::App {
            fun: Box::new(n),
            args: a.to_vec(),
        }
    }

    pub fn if_then_else(c: ML, t: ML, o: ML) -> Self {
        Self::IfThenElse {
            cond: Box::new(c),
            then: Box::new(t),
            or: Some(Box::new(o)),
        }
    }

    pub fn cond(c: ML, t: ML, o: Option<ML>) -> Self {
        Self::IfThenElse {
            cond: Box::new(c),
            then: Box::new(t),
            or: o.map(Box::new),
        }
    }
}

static COUNTER: AtomicUsize = AtomicUsize::new(0);
pub fn gensym() -> String {
    let v = COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    format!("v_{v}")
}

/// Alpha Conversion: Ensure each variable name appears _once_,
/// ie
///    (let x 5 (let x 4 (f x)))
/// =>
///    (let x 5 (let y 4 (f y)))
/// make many conversions later on a lot easier. The price we pay
/// is some unsightly variable names.
pub fn alpha_convert(ml: ML) -> ML {
    fn alpha_convert_(ml: ML, subs: &mut Vec<(Var, Var)>) -> ML {
        match ml {
            // These need no renaming
            ML::Real(_) | ML::Bool(_) | ML::Unit => ml,
            ML::Fun {
                name,
                args,
                body,
                rest,
            } => {
                let alt = gensym();
                subs.push((name.clone(), alt.clone()));
                // Generate a new vector of formal args for the duration of the call
                let mut new = Vec::new();
                let mut idx = Vec::new();
                for arg in &args {
                    let repl = gensym();
                    idx.push(new.len());
                    subs.push((arg.to_string(), repl.clone()));
                    new.push(repl);
                }
                let res = ML::fun(
                    &alt,
                    &new,
                    alpha_convert_(*body, subs),
                    alpha_convert_(*rest, subs),
                );
                for _ in &args {
                    subs.pop();
                }
                // remove name
                subs.pop();
                res
            }
            // Just recurse into its subterms
            ML::App { fun, args } => {
                let args = args
                    .into_iter()
                    .map(|a| alpha_convert_(a, subs))
                    .collect::<Vec<_>>();
                let fun = alpha_convert_(*fun, subs);
                ML::app(fun, &args)
            }
            // Just recurse into its subterms
            ML::IfThenElse { cond, then, or } => ML::cond(
                alpha_convert_(*cond, subs),
                alpha_convert_(*then, subs),
                or.map(|o| alpha_convert_(*o, subs)),
            ),
            // In a scoped let, we rename the variable for the time of the call
            ML::Let { name, value, body } => {
                let repl = gensym();
                subs.push((name, repl.clone()));
                let res = ML::val(
                    repl,
                    alpha_convert_(*value, subs),
                    alpha_convert_(*body, subs),
                );
                subs.pop();
                res
            }
            // NOTE: A set! to a fresh variable cannot be renamed, since it's a global thing.
            // Example (do
            //          (set! x 42)
            //          (+ x x))
            //  Thus, we never introduce new variable on set! and never purge them.
            //  However set!ting a known variable need substitution.
            ML::Set { name, value } => {
                if let Some(p) = subs.iter().find(|p| p.0 == name) {
                    ML::set(p.1.clone(), alpha_convert_(*value, subs))
                } else {
                    ML::set(name, alpha_convert_(*value, subs))
                }
            }
            // If we see a variable we replace it with the last renaming, if any
            ML::Var(n) => {
                if let Some(p) = subs.iter().rev().find(|p| n == p.0) {
                    ML::var(p.1.clone())
                } else {
                    ML::var(n)
                }
            }
            // Seq just recurses into its subterms while accumulating into subs!
            ML::Seq(es) => ML::seq(
                &es.into_iter()
                    .map(|e| alpha_convert_(e, subs))
                    .collect::<Vec<_>>(),
            ),
        }
    }
    alpha_convert_(ml, &mut Vec::new())
}

// Values
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Val {
    Unit,
    Bool(bool),
    Real(String),
}

impl TryFrom<ML> for Val {
    type Error = &'static str;

    fn try_from(ml: ML) -> std::result::Result<Self, Self::Error> {
        match ml {
            ML::Unit => Ok(Val::Unit),
            ML::Bool(b) => Ok(Val::Bool(b)),
            ML::Real(s) => Ok(Val::Real(s)),
            _ => todo!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Term {
    Var(Var),
    LetVal {
        name: Var,
        value: Val,
        body: Box<Term>,
    },
    LetCnt {
        name: Var,
        args: Vec<Var>,
        body: Box<Term>,
        rest: Box<Term>,
    },
    // TODO comtemplate whether it would be better to use single argument
    // functions only. Reason: Single known arguments can now be (partially)
    // applied, a capability we do not have with the multi-arg variant.
    LetFun {
        name: Var,
        cont: Var,
        args: Vec<Var>,
        body: Box<Term>,
        rest: Box<Term>,
    },
    AppCnt {
        name: Var,
        args: Vec<Var>,
    },
    AppFun {
        name: Var,
        cont: Var,
        args: Vec<Var>,
    },
    IfElse {
        cond: Var,
        then: CVar,
        or: CVar,
    },
    Return(Var),
}

impl Term {
    pub fn var<V>(v: V) -> Self
    where
        Var: From<V>,
    {
        Term::Var(Var::from(v))
    }

    pub fn let_val<V>(n: V, v: Val, b: Term) -> Self
    where
        Var: From<V>,
    {
        Self::LetVal {
            name: n.into(),
            value: v,
            body: Box::new(b),
        }
    }

    pub fn let_fun<V, C>(name: V, cont: C, args: &[&str], body: Term, rest: Term) -> Self
    where
        V: AsRef<str>,
        C: AsRef<str>,
    {
        Self::LetFun {
            name: name.as_ref().into(),
            cont: cont.as_ref().into(),
            args: args.iter().map(|arg| Var::from(*arg)).collect(),
            body: Box::new(body),
            rest: Box::new(rest),
        }
    }

    pub fn let_cnt<V>(name: V, args: &[&str], body: Term, rest: Term) -> Self
    where
        V: AsRef<str>,
    {
        Self::LetCnt {
            name: name.as_ref().into(),
            args: args.iter().map(|&arg| Var::from(arg)).collect(),
            body: Box::new(body),
            rest: Box::new(rest),
        }
    }

    pub fn app_cnt(n: &str, a: &[Var]) -> Self {
        Self::AppCnt {
            name: n.to_string(),
            args: a.to_vec(),
        }
    }

    pub fn ret<V>(name: V) -> Self
    where
        V: AsRef<str>,
    {
        Self::Return(name.as_ref().into())
    }

    pub fn app_fun(name: &str, cont: &str, args: &[Var]) -> Self {
        Self::AppFun {
            name: name.to_string(),
            cont: cont.to_string(),
            args: args.to_vec(),
        }
    }

    pub fn if_then_else<C, T, O>(cond: C, then: T, or: O) -> Self
    where
        C: AsRef<str>,
        T: AsRef<str>,
        O: AsRef<str>,
    {
        Term::IfElse {
            cond: Var::from(cond.as_ref()),
            then: Var::from(then.as_ref()),
            or: Var::from(or.as_ref()),
        }
    }
}

pub type Cont<'a> = Box<dyn FnOnce(&str) -> Term + 'a>;

pub fn cps(ml: ML, k: Cont<'_>) -> Term {
    match ml {
        ML::Real(_) | ML::Bool(_) | ML::Unit => {
            let name = gensym();
            let body = k(&name);
            Term::let_val(&name, Val::try_from(ml).unwrap(), body)
        }
        ML::Var(name) => k(&name),
        ML::Let { name, value, body } => {
            let kont = gensym();
            Term::let_cnt(&kont, &[&name], cps(*body, k), kps(*value, &kont))
        }
        ML::Fun {
            name,
            args,
            body,
            rest,
        } => {
            let cont = gensym();
            Term::LetFun {
                name,
                cont: cont.clone(),
                args,
                body: Box::new(kps(*body, &cont)),
                rest: Box::new(cps(*rest, k)),
            }
        }
        ML::IfThenElse {
            cond,
            then,
            or: Some(or),
        } => {
            let x = gensym();
            let halt = gensym();
            let on_true = gensym();
            let on_false = gensym();
            cps(
                *cond,
                Box::new(|z| {
                    Term::let_cnt(
                        &halt,
                        &[&x],
                        k(&x),
                        Term::let_cnt(
                            &on_true,
                            &[],
                            kps(*then, &halt),
                            Term::let_cnt(
                                &on_false,
                                &[],
                                kps(*or, &halt),
                                Term::if_then_else(z, &on_true, &on_false),
                            ),
                        ),
                    )
                }),
            )
        }
        ML::IfThenElse {
            cond,
            then,
            or: None,
        } => {
            let x = gensym();
            let halt = gensym();
            let on_true = gensym();
            cps(
                *cond,
                Box::new(|z| {
                    Term::let_cnt(
                        &halt,
                        &[&x],
                        k(&x),
                        Term::let_cnt(
                            &on_true,
                            &[],
                            kps(*then, &halt),
                            Term::if_then_else(z, &on_true, &halt),
                        ),
                    )
                }),
            )
        }
        ML::App { fun, args } => {
            fn make_app(
                idx: usize,
                args: &Vec<ML>,
                vars: Vec<String>,
                f: &str,
                halt: Cont,
            ) -> Term {
                if idx >= args.len() {
                    let name = gensym();
                    let x = gensym();
                    Term::let_cnt(&name, &[&x], halt(&x), Term::app_fun(f, &name, &vars))
                } else {
                    cps(
                        args[idx].clone(),
                        Box::new(|x| {
                            let mut vars = vars.clone();
                            vars.push(x.to_string());
                            make_app(idx + 1, args, vars, f, halt)
                        }),
                    )
                }
            }
            cps(*fun, Box::new(|f| make_app(0, &args, Vec::new(), f, k)))
        }
        ML::Set { .. } => todo!(),
        ML::Seq(_) => todo!(),
    }
}

pub fn kps(ml: ML, k: &str) -> Term {
    match ml {
        ML::Real(_) | ML::Bool(_) | ML::Unit => {
            let name = gensym();
            Term::let_val(
                &name,
                Val::try_from(ml).unwrap(),
                Term::app_cnt(k, &[name.clone()]),
            )
        }
        ML::Var(v) => Term::app_cnt(k, &[v]),
        ML::Fun {
            name,
            args,
            body,
            rest,
        } => {
            let cont = gensym();
            Term::LetFun {
                name,
                cont: cont.clone(),
                args,
                body: Box::new(kps(*body, &cont)),
                rest: Box::new(kps(*rest, k)),
            }
        }
        ML::Let { name, value, body } => {
            let kont = gensym();
            Term::let_cnt(&kont, &[&name], kps(*body, k), kps(*value, &kont))
        }
        ML::IfThenElse {
            cond,
            then,
            or: Some(or),
        } => {
            let on_true = gensym();
            let on_false = gensym();
            cps(
                *cond,
                Box::new(|z| {
                    Term::let_cnt(
                        &on_true,
                        &[],
                        kps(*then, k),
                        Term::let_cnt(
                            &on_false,
                            &[],
                            kps(*or, k),
                            Term::if_then_else(z, &on_true, &on_false),
                        ),
                    )
                }),
            )
        }
        ML::IfThenElse {
            cond,
            then,
            or: None,
        } => {
            let on_true = gensym();
            cps(
                *cond,
                Box::new(|z| {
                    Term::let_cnt(
                        &on_true,
                        &[],
                        kps(*then, k),
                        Term::if_then_else(z, &on_true, k),
                    )
                }),
            )
        }
        ML::App { fun, args } => {
            fn make_app(
                idx: usize,
                args: &Vec<ML>,
                vars: Vec<String>,
                f: &str,
                halt: &str,
            ) -> Term {
                if idx >= args.len() {
                    Term::app_fun(f, halt, &vars)
                } else {
                    cps(
                        args[idx].clone(),
                        Box::new(|x| {
                            let mut vars = vars.clone();
                            vars.push(x.to_string());
                            make_app(idx + 1, args, vars, f, halt)
                        }),
                    )
                }
            }
            cps(*fun, Box::new(|f| make_app(0, &args, Vec::new(), f, k)))
        }
        ML::Set { .. } => todo!(),
        ML::Seq(_) => todo!(),
    }
}

pub fn ml_to_cps(ml: ML) -> Term {
    cps(ml, Box::new(|s| Term::ret(s)))
}

impl Display for Val {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Val::Unit => write!(f, "()"),
            Val::Bool(b) => write!(f, "{b}"),
            Val::Real(r) => write!(f, "{r}"),
        }
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Var(v) => write!(f, "{}", v),
            Term::LetVal { name, value, body } => write!(f, "(let-val {name} {value} {body})"),
            Term::LetCnt {
                name,
                args,
                body,
                rest,
            } => write!(f, "(let-cnt {name} ({}) {body} {rest})", args.join(", ")),
            Term::LetFun {
                name,
                cont,
                args,
                body,
                rest,
            } => write!(
                f,
                "(let-fun {name} [{cont}] ({}) {body} {rest})",
                args.join(", ")
            ),
            Term::AppCnt { name, args } => write!(f, "({name} {})", args.join(", ")),
            Term::AppFun { name, cont, args } => write!(f, "({name} [{cont}] {})", args.join(", ")),
            Term::IfElse { cond, then, or } => write!(f, "(if {cond} {then} {or})"),
            Term::Return(r) => write!(f, "(return {r})"),
        }
    }
}

/// Substitute Variables for Variables. (term[x=y])
/// Will replace any occurence of name `x` with name `y`.
/// Used to (partially?) apply functions.
/// Example:
/// (app
///   (fun [x] k
///      (return x))
///   y)
/// =>
///   (return x)[x=y]
/// =>
///   (return y)
pub fn substitute(term: Term, lut: &Map<Var, Var>) -> Result<Term> {
    let lookup = |key: &Var| -> Var { lut.get(key).unwrap_or(key).to_string() };
    let term = match term {
        Term::Var(var) => Term::var(lookup(&var)),
        Term::LetVal { name, value, body } => {
            Term::let_val(name, value.clone(), substitute(*body, lut)?)
        }
        Term::LetCnt {
            name,
            args,
            body,
            rest,
        } => Term::let_cnt(
            name,
            &args.iter().map(String::as_str).collect::<Vec<_>>(),
            substitute(*body, lut)?,
            substitute(*rest, lut)?,
        ),
        Term::LetFun {
            name,
            args,
            body,
            rest,
            cont,
        } => Term::let_fun(
            name,
            lookup(&cont),
            &args.iter().map(String::as_str).collect::<Vec<_>>(),
            substitute(*body, lut)?,
            substitute(*rest, lut)?,
        ),
        Term::AppCnt { name, args } => Term::app_cnt(
            &lookup(&name),
            &args.iter().map(lookup).collect::<Vec<_>>(),
        ),
        Term::AppFun { name, cont, args } => Term::app_fun(
            &lookup(&name),
            &lookup(&cont),
            &args.iter().map(lookup).collect::<Vec<_>>(),
        ),
        Term::IfElse { cond, then, or } => {
            Term::if_then_else(lookup(&cond), lookup(&then), lookup(&or))
        }
        Term::Return(what) => Term::ret(lookup(&what)),
    };
    Ok(term)
}

/// constant propagation for values
/// Expand known values going down the tree.
/// Collapse if-then-else over known conditions.
/// TODO Expand into primitives.
/// Example:
/// (let c true
///   (if c
///    x
///    y))
/// =>
///   (app x [])
pub fn constant(term: Term) -> Result<Term> {
    let mut lut = Map::new();
    fn do_constant(term: Term, lut: &mut Map<Var, Val>) -> Result<Term> {
        let res = match &term {
            Term::Var(_) => term,
            Term::LetVal { name, value, body } => {
                if lut.contains_key(name) {
                    return Err(ModcxxError::InternalError(format!(
                        "program not alphatized, found (let {name} ...) at least twice."
                    )));
                }
                lut.insert(name.to_string(), value.clone());
                let res = do_constant(*body.clone(), lut)?;
                lut.remove(name);
                res
            }
            Term::LetCnt {
                name,
                args,
                body,
                rest,
            } => Term::let_cnt(
                name,
                &args.iter().map(String::as_str).collect::<Vec<_>>(),
                do_constant(*body.clone(), lut)?,
                do_constant(*rest.clone(), lut)?,
            ),
            Term::LetFun {
                name,
                cont,
                args,
                body,
                rest,
            } => Term::let_fun(
                name,
                cont,
                &args.iter().map(String::as_str).collect::<Vec<_>>(),
                do_constant(*body.clone(), lut)?,
                do_constant(*rest.clone(), lut)?,
            ),
            Term::IfElse { cond, then, or } => match lut.get(cond) {
                Some(Val::Bool(true)) => Term::app_cnt(then, &[]),
                Some(Val::Bool(false)) => Term::app_cnt(or, &[]),
                Some(Val::Unit) => Term::app_cnt(or, &[]),
                Some(Val::Real(r)) if r.parse::<f64>().unwrap() == 0.0 => Term::app_cnt(or, &[]),
                Some(Val::Real(_)) => Term::app_cnt(then, &[]),
                None => term,
            },
            Term::AppCnt { .. } => term,
            Term::AppFun { .. } => term,
            Term::Return(_) => term,
        };
        Ok(res)
    }

    do_constant(term, &mut lut)
}

/// beta-expansion aka inlining
pub fn beta(term: Term) -> Result<Term> {
    fn do_beta(
        term: Term,
        funs: &mut Map<String, (String, Vec<String>, Term)>,
        cnts: &mut Map<String, (Vec<String>, Term)>,
    ) -> Result<Term> {
        let res = match &term {
            Term::LetVal { name, value, body } => {
                Term::let_val(name, value.clone(), do_beta(*body.clone(), funs, cnts)?)
            }
            Term::LetCnt {
                name,
                args,
                body,
                rest,
            } => Term::let_cnt(
                name,
                &args.iter().map(String::as_str).collect::<Vec<_>>(),
                do_beta(*body.clone(), funs, cnts)?,
                do_beta(*rest.clone(), funs, cnts)?,
            ),
            Term::LetFun {
                name,
                cont,
                args,
                body,
                rest,
            } => Term::let_fun(
                name,
                cont,
                &args.iter().map(String::as_str).collect::<Vec<_>>(),
                do_beta(*body.clone(), funs, cnts)?,
                do_beta(*rest.clone(), funs, cnts)?,
            ),
            Term::AppCnt { name, args } => {
                let (vals, body) = cnts.get(name).ok_or(ModcxxError::InternalError(format!(
                    "continuation {name} not found in term {term}."
                )))?;
                let lut = vals
                    .iter()
                    .cloned()
                    .zip(args.iter().cloned())
                    .collect::<Map<_, _>>();
                substitute(body.clone(), &lut)?
            }
            Term::AppFun { name, cont, args } => {
                let (kont, vals, body) = funs
                    .get(name)
                    .unwrap_or_else(|| panic!("function {name} not found."));
                let mut lut = vals
                    .iter()
                    .map(|v| v.to_string())
                    .zip(args.iter().map(|v| v.to_string()))
                    .collect::<Map<_, _>>();
                lut.insert(cont.to_string(), kont.to_string());
                substitute(body.clone(), &lut)?
            }
            Term::IfElse { .. } | Term::Var(_) | Term::Return(_) => term,
        };
        Ok(res)
    }
    do_beta(term, &mut Map::new(), &mut Map::new())
}

/// Eliminate dead code
/// Traverse the tree and match (let x ... (use x)) pairs. If there's no usage,
/// we eliminate the binding site.
pub fn eliminate_dead_code(term: Term) -> Result<Term> {
    fn do_dead_code(term: Term, lut: &mut Map<Var, usize>) -> Result<Term> {
        let mut bump = |k: &str| {
            *lut.entry(k.to_string()).or_default() += 1;
        };
        let res = match &term {
            Term::Var(v) => {
                bump(v);
                term
            }
            Term::LetVal { name, value, body } => {
                let old = *lut.entry(name.to_string()).or_default();
                let body = do_dead_code(*body.clone(), lut)?;
                let new = *lut.entry(name.to_string()).or_default();
                if old == new {
                    body
                } else {
                    Term::let_val(name, value.clone(), body)
                }
            }
            Term::LetCnt {
                name,
                args,
                body,
                rest,
            } => {
                let mut inner = Map::new();
                let body = do_dead_code(*body.clone(), &mut inner)?;
                let old = *lut.entry(name.to_string()).or_default();
                let rest = do_dead_code(*rest.clone(), lut)?;
                let new = *lut.entry(name.to_string()).or_default();
                if old == new {
                    rest
                } else {
                    inner
                        .into_iter()
                        .for_each(|(k, v)| *lut.entry(k.to_string()).or_default() += v);
                    Term::let_cnt(
                        name,
                        &args.iter().map(String::as_str).collect::<Vec<_>>(),
                        body,
                        rest,
                    )
                }
            }
            Term::LetFun {
                name,
                cont,
                args,
                body,
                rest,
            } => {
                let mut inner = Map::new();
                let body = do_dead_code(*body.clone(), &mut inner)?;
                let old = *lut.entry(name.to_string()).or_default();
                let rest = do_dead_code(*rest.clone(), lut)?;
                let new = *lut.entry(name.to_string()).or_default();
                if old == new {
                    rest
                } else {
                    inner
                        .into_iter()
                        .for_each(|(k, v)| *lut.entry(k.to_string()).or_default() += v);
                    Term::let_fun(
                        name,
                        cont,
                        &args.iter().map(String::as_str).collect::<Vec<_>>(),
                        body,
                        rest,
                    )
                }
            }
            Term::AppCnt { name, args } => {
                bump(name);
                args.iter().for_each(|k| bump(k));
                term
            }
            Term::AppFun { name, cont, args } => {
                bump(name);
                bump(cont);
                args.iter().for_each(|k| bump(k));
                term
            }
            Term::IfElse { cond, then, or } => {
                bump(cond);
                bump(then);
                bump(or);
                term
            }
            Term::Return(name) => {
                bump(name);
                term
            }
        };
        Ok(res)
    }
    do_dead_code(term, &mut Map::new())
}

fn to_cxx(term: &Term) -> String {
    fn do_to_cxx(
        term: &Term,
        ind: usize,
        continuations: &mut Map<String, (Vec<String>, Term)>,
    ) -> String {
        match term {
            Term::Var(x) => x.to_string(),
            Term::LetVal { name, value, body } => {
                let body = do_to_cxx(body, ind, continuations);
                match value {
                    Val::Unit => format!("{:ind$}void* {name} = nullptr;\n{body}", ""),
                    Val::Bool(b) => format!("{:ind$}bool {name} = {b};\n{body}", ""),
                    Val::Real(r) => format!("{:ind$}double {name} = {r};\n{body}", ""),
                }
            }
            Term::LetCnt {
                name,
                args,
                body,
                rest,
            } => {
                continuations.insert(name.to_string(), (args.clone(), *body.clone()));
                let res = do_to_cxx(rest, ind, continuations);
                continuations.remove(name);
                res
            }
            Term::LetFun {
                name,
                cont,
                args,
                body,
                rest,
            } => {
                let var = gensym();
                continuations.insert(cont.to_string(), (vec![var.to_string()], Term::ret(var)));
                let body = do_to_cxx(body, ind + 4, continuations);
                let rest = do_to_cxx(rest, ind + 4, continuations);
                let args = args.join(", ");

                format!("{:ind$}void {name}({args}) {{\n{body}\n{:ind$}}}\n\nint main () {{\n{rest}\n}}", "", "")
            }
            Term::AppCnt { name, args } => {
                let (vals, body) = continuations
                    .get(name)
                    .unwrap_or_else(|| panic!("continuation {name} not found."));
                let lut = vals
                    .iter()
                    .cloned()
                    .zip(args.iter().cloned())
                    .collect::<Map<_, _>>();
                let term = substitute(body.clone(), &lut).unwrap();
                do_to_cxx(&term, ind, continuations)
            }
            Term::AppFun { name, cont, args } => {
                let var = gensym();
                let (vals, body) = continuations
                    .get(cont)
                    .unwrap_or_else(|| panic!("continuation {cont} not found."));
                let lut = vals
                    .iter()
                    .cloned()
                    .zip([var.to_string()])
                    .collect::<Map<_, _>>();
                let term = substitute(body.clone(), &lut).unwrap();
                let rest = do_to_cxx(&term, ind, continuations);
                let args = args.join(", ");
                format!("{:ind$}double {var} = {name}({args});\n{rest}", "")
            }
            Term::IfElse { cond, then, or } => {
                let (vals, then) = continuations
                    .get(then)
                    .as_ref()
                    .unwrap_or_else(|| panic!("continuation {then} not found."));
                assert!(vals.is_empty());
                let then = do_to_cxx(&then.clone(), ind + 4, continuations);
                let (vals, or) = continuations
                    .get(or)
                    .unwrap_or_else(|| panic!("continuation {or} not found."));
                assert!(vals.is_empty());
                let or = do_to_cxx(&or.clone(), ind + 4, continuations);
                format!(
                    "{:ind$}if ({cond}) {{\n{then}\n{:ind$}}}\n{:ind$}else {{\n{or}\n{:ind$}}}",
                    "", "", "", ""
                )
            }
            Term::Return(x) => format!("{:ind$}return {x};", ""),
        }
    }
    do_to_cxx(term, 0, &mut Map::new())
}

pub fn reduce(term: Term) -> Result<Term> {
    let mut term = term;
    loop {
        let new = beta(term.clone())?;
        let new = eliminate_dead_code(new)?;
        if new == term {
            return Ok(new);
        }
        term = new;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cps_simple_expressions() {
        let ml = ML::fun(
            "f",
            &["x"],
            ML::var("x"),
            ML::app(
                ML::var("g"),
                &[ML::if_then_else(
                    ML::bool(true),
                    ML::app(ML::var("f"), &[ML::real("23")]),
                    ML::app(ML::var("f"), &[ML::var("z")]),
                )],
            ),
        );
        let cps = ml_to_cps(ml.clone());
        let cxx = to_cxx(&cps);
        println!("{cps}");
        println!("{cxx}");
        /*
         * (let-fun f [v_0] (x)
         *     (v_0 x)
         *   (let-cnt v_2 (v_1)
         *        (let-cnt v_5 (v_6)
         *            (return v_6)
         *          (g [v_5] v_1))
         *      (let-cnt v_3 ()
         *           (f [v_2] y)
         *         (let-cnt v_4 ()
         *              (f [v_2] z)
         *            (if d v_3 v_4)))))
         */
        let cps = reduce(cps).unwrap();
        let cxx = to_cxx(&cps);
        println!("{cps}");
        println!("{cxx}");
    }
}
