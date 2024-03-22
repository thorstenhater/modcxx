use std::cell::RefCell;
use std::collections::BTreeSet;
use std::fmt;
use std::sync::atomic::AtomicUsize;

type Set<T> = BTreeSet<T>;

// Nomrmal Variables.
pub type Var = String;
// Continuation Variables. Live in a different Environment
pub type CVar = String;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ML {
    Real(String),
    Bool(bool),
    Unit,
    Lam {
        args: Vec<Var>,
        term: Box<ML>,
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

    pub fn fun<V>(a: &[V], b: ML) -> Self
    where
        Var: From<V>,
        V: Clone,
    {
        Self::Lam {
            args: a.iter().cloned().map(|x| Var::from(x)).collect(),
            term: Box::new(b),
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

fn alpha_convert_(ml: ML, subs: &mut Vec<(Var, Var)>) -> ML {
    match ml {
        // These need no renaming
        ML::Real(_) | ML::Bool(_) | ML::Unit => ml,
        ML::Lam { args, term } => {
            // Generate a new vector of formal args for the duration of the call
            let mut new = Vec::new();
            let mut idx = Vec::new();
            for arg in &args {
                let repl = gensym();
                idx.push(new.len());
                subs.push((arg.to_string(), repl.clone()));
                new.push(repl);
            }
            let res = ML::fun(&new, alpha_convert_(*term, subs));
            for _ in &args {
                subs.pop();
            }
            res
        }
        // Just recurse into its subterms
        ML::App { fun, args } => ML::app(
            alpha_convert_(*fun, subs),
            &args
                .into_iter()
                .map(|a| alpha_convert_(a, subs))
                .collect::<Vec<_>>(),
        ),
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

/// Alpha Conversion: Ensure each variable name appears _once_,
/// ie
///    (let x 5 (let x 4 (f x)))
/// =>
///    (let x 5 (let y 4 (f y)))
/// make many conversions later on a lot easier. The price we pay
/// is some unsightly variable names.
pub fn alpha_convert(ml: ML) -> ML {
    alpha_convert_(ml, &mut Vec::new())
}

// Values
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Val {
    Unit,
    Bool(bool),
    Real(String),
}

impl Val {
    fn to_cxx(&self) -> String {
        match self {
            Val::Unit => String::from("void"),
            Val::Bool(b) => format!("{b}"),
            Val::Real(r) => r.to_string(),
        }
    }

   fn to_type(&self) -> String {
        match self {
            Val::Unit => String::from("void"),
            Val::Bool(_) => String::from("bool"),
            Val::Real(_) => String::from("double"),
        }
    }
}

impl fmt::Display for Val {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Val::Unit => write!(f, "()"),
            Val::Bool(v) => write!(f, "{v}"),
            Val::Real(v) => write!(f, "{v}"),
        }
    }
}

impl TryFrom<ML> for Val {
    type Error = &'static str;

    fn try_from(ml: ML) -> Result<Self, Self::Error> {
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
        term: Box<Term>,
        body: Box<Term>,
    },
    LetFun {
        name: Var,
        cont: Var,
        args: Vec<Var>,
        term: Box<Term>,
        body: Box<Term>,
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
    SetThen{
        name: Var,
        value: Var,
        body: Box<Term>,
    },
}

impl Term {
    pub fn to_cxx(&self, ind: usize) -> String {
        match self {
            Term::Var(v) => v.to_string(),
            Term::LetVal { name, value, body } => {
                let ty = value.to_type();
                let value = value.to_cxx();
                let rest = body.to_cxx(ind);
                format!("{ty} {name} = {value};\n{rest}")
            }
            Term::SetThen { name, value, body } => {
                let rest = body.to_cxx(ind);
                format!("{name} = {value};\n{rest}")
            }
            _ => String::from("???"),
        }
    }

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

    pub fn let_fun(n: Var, c: Var, a: &[Var], t: Term, b: Term) -> Self {
        Self::LetFun {
            name: n,
            cont: c,
            args: a.to_vec(),
            term: Box::new(t),
            body: Box::new(b),
        }
    }

    pub fn let_cnt(n: Var, a: &[Var], v: Term, b: Term) -> Self {
        Self::LetCnt {
            name: n,
            args: a.to_vec(),
            term: Box::new(v),
            body: Box::new(b),
        }
    }

    pub fn app_cnt(n: Var, a: &[Var]) -> Self {
        Self::AppCnt {
            name: n,
            args: a.to_vec(),
        }
    }

    pub fn app_fun(n: Var, c: Var, a: &[Var]) -> Self {
        Self::AppFun {
            name: n,
            cont: c,
            args: a.to_vec(),
        }
    }

    pub fn if_then_else(c: Var, t: CVar, o: CVar) -> Self {
        Term::IfElse {
            cond: c,
            then: t,
            or: o,
        }
    }

    pub fn set_then<U, V>(n: U, v: V, b: Term) -> Self
    where
        Var: From<U>,
        Var: From<V>,
    {
        Term::SetThen {
            name: Var::from(n),
            value: Var::from(v),
            body: Box::new(b),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Term::Var(v) => write!(f, "{v}"),
            Term::LetVal { name, value, body } => write!(f, "(let [{name} {value}] {body})"),
            Term::LetFun {
                name,
                cont,
                args,
                term,
                body,
            } => write!(
                f,
                "(let [{name} {cont} ({}) {term}] {body})",
                args.join(" ")
            ),
            Term::LetCnt {
                name,
                args,
                term,
                body,
            } => write!(f, "(let [{name} ({}) {term}] {body})", args.join(" ")),
            Term::AppCnt { name, args } => write!(f, "({name} [{}])", args.join(" ")),
            Term::AppFun { name, cont, args } => write!(f, "({name} {cont} {})", args.join(" ")),
            Term::IfElse { cond, then, or } => write!(f, "(if {cond} {then} {or}]"),
            Term::SetThen { name, value, body } => write!(f, "(set! {name} {value} {body}]"),
        }
    }
}

pub type Cont<'a> = Box<dyn FnOnce(Var) -> Term + 'a>;

pub fn cps(ml: ML, k: Cont<'_>) -> Term {
    match ml {
        e @ (ML::Real(_) | ML::Bool(_) | ML::Unit) => {
            let x = gensym();
            let b = k(x.clone());
            let v = e.try_into().unwrap();
            Term::let_val(x, v, b)
        }
        ML::Var(v) => k(v),
        ML::App { fun, args } => {
            let nargs = vec![RefCell::new(String::new()); args.len()];
            let mut k: Cont<'_> = Box::new(|z| {
                let c = gensym();
                let x = gensym();
                let args = nargs.iter().map(|c| c.take()).collect::<Vec<_>>();
                Term::let_cnt(c.clone(), &[x.clone()], k(x), Term::app_fun(z, c, &args))
            });
            let mut term = *fun;
            for (arg, narg) in args.iter().cloned().zip(nargs.iter()).rev() {
                k = Box::new(|x| {
                    narg.replace(x);
                    cps(term, k)
                });
                term = arg;
            }
            cps(term, k)
        }
        ML::Lam { args, term } => {
            let n = gensym();
            let c = gensym();
            Term::let_fun(n.clone(), c.clone(), &args, kps(*term, c), k(n))
        }
        ML::Let { name, value, body } => {
            let j = gensym();
            Term::let_cnt(j.clone(), &[name], cps(*body, k), kps(*value, j))
        }
        ML::Set { name, value } => cps(
            *value,
            Box::new(|a| Term::set_then(name, a, k("nil".to_string()))),
        ),
        ML::IfThenElse { cond, then, or } => {
            let j = gensym();
            let x = gensym();
            let t = gensym();
            let xt = gensym();
            let o = gensym();
            let xo = gensym();
            let or = or.map(|o| *o).unwrap_or(ML::Unit);
            cps(
                *cond,
                Box::new(|z| {
                    Term::let_cnt(
                        j.clone(),
                        &[x.clone()],
                        k(x),
                        Term::let_cnt(
                            t.clone(),
                            &[xt.clone()],
                            kps(*then, j.clone()),
                            Term::let_cnt(
                                o.clone(),
                                &[xo.clone()],
                                kps(or, j),
                                Term::if_then_else(z, t, o),
                            ),
                        ),
                    )
                }),
            )
        }
        ML::Seq(es) => {
            let Some((e, es)) = es.split_first()
            else {
                unreachable!()
            };
            if es.is_empty() {
                cps(e.clone(), k)
            } else {
                cps(e.clone(), Box::new(|_| cps(ML::Seq(es.to_vec()), k)))
            }
        }
    }
}

pub fn kps(ml: ML, k: CVar) -> Term {
    match ml {
        e @ (ML::Real(_) | ML::Bool(_) | ML::Unit) => {
            let x = gensym();
            let b = Term::app_cnt(k, &[x.clone()]);
            let v = e.try_into().unwrap();
            Term::let_val(x, v, b)
        }
        ML::Var(v) => Term::app_cnt(k, &[v]),
        ML::App { fun, args } => {
            let nargs = vec![RefCell::new(String::new()); args.len()];
            let mut k: Cont<'_> = Box::new(|z| {
                let args = nargs.iter().map(|c| c.take()).collect::<Vec<_>>();
                Term::app_fun(z, k.clone(), &args)
            });
            let mut term = *fun;
            for (arg, narg) in args.iter().cloned().zip(nargs.iter()).rev() {
                k = Box::new(|x| {
                    narg.replace(x);
                    cps(term, k)
                });
                term = arg;
            }
            cps(term, k)
        }
        ML::Lam { args, term } => {
            let f = gensym();
            let j = gensym();
            Term::let_fun(
                f.clone(),
                j.clone(),
                &args,
                kps(*term, j),
                Term::app_cnt(k, &[f]),
            )
        }
        ML::Let { name, value, body } => {
            let j = gensym();

            Term::let_cnt(j.clone(), &[name], kps(*body, k), kps(*value, j))
        }
        ML::IfThenElse { cond, then, or } => {
            let t = gensym();
            let xt = gensym();
            let o = gensym();
            let xo = gensym();
            let or = or.map(|o| *o).unwrap_or(ML::Unit);
            cps(
                *cond,
                Box::new(|z| {
                    Term::let_cnt(
                        t.clone(),
                        &[xt.clone()],
                        kps(*then, k.clone()),
                        Term::let_cnt(
                            o.clone(),
                            &[xo.clone()],
                            kps(or, k),
                            Term::if_then_else(z, t, o),
                        ),
                    )
                }),
            )
        }
        ML::Seq(es) => {
            let Some((e, es)) = es.split_first()
            else {
                unreachable!()
            };
            if es.is_empty() {
                kps(es[0].clone(), k)
            } else {
                cps(e.clone(), Box::new(|_| kps(ML::Seq(es.to_vec()), k)))
            }
        }
        ML::Set { name, value } => cps(
            *value,
            Box::new(|a| Term::set_then(name, a, Term::app_cnt(k, &[]))),
        ),
    }
}

pub fn dead_code(term: Term) -> Term {
    match term {
        Term::LetVal { name, body, value } => {
            let body = dead_code(*body);
            if used(&body).contains(&name) {
                Term::let_val(name, value.clone(), body)
            } else {
                body
            }
        }
        Term::LetFun {
            name,
            cont,
            args,
            term,
            body,
        } => {
            let body = dead_code(*body);
            if used(&body).contains(&name) {
                Term::let_fun(name, cont, &args, dead_code(*term), body)
            } else {
                body
            }
        }
        Term::LetCnt {
            name,
            args,
            term,
            body,
        } => {
            let body = dead_code(*body);
            if used(&body).contains(&name) {
                let term = dead_code(*term);
                Term::let_cnt(name, &args, term, body)
            } else {
                body
            }
        }
        // NOTE set! cannot be removed. It's a side-effect;
        // the rest is operating purely on names, not terms.
        _ => term,
    }
}

fn used(term: &Term) -> Set<Var> {
    let mut res = Set::new();
    fn used_(term: &Term, seen: &mut Set<Var>) {
        match term {
            Term::Var(v) => {
                seen.insert(v.to_string());
            }
            Term::LetVal { body, .. } => used_(body, seen),
            Term::LetFun { body, .. } => used_(body, seen),
            Term::LetCnt { body, .. } => used_(body, seen),
            Term::AppCnt { name, args } => {
                seen.insert(name.to_string());
                for arg in args {
                    seen.insert(arg.to_string());
                }
            }
            Term::AppFun { name, cont, args } => {
                seen.insert(name.to_string());
                seen.insert(cont.to_string());
                for arg in args {
                    seen.insert(arg.to_string());
                }
            }
            Term::IfElse { cond, then, or } => {
                seen.insert(cond.to_string());
                seen.insert(then.to_string());
                seen.insert(or.to_string());
            }
            Term::SetThen { name, body, .. } => {
                seen.insert(name.to_string());
                used_(body, seen);
            }
        }
    }
    used_(term, &mut res);
    res
}

fn propagate_values(term: Term) -> Term {
    propagate_values_(term, &mut Vec::new())
}

fn propagate_values_(term: Term, map: &mut Vec<(String, Val)>) -> Term {
    match term {
        Term::Var(v) => todo!(),
        Term::LetVal { name, value, body } => {
            map.push((name.clone(), value.clone()));
            let res = propagate_values_(*body, map);
            map.pop();
            res
        }
        Term::LetFun {
            name,
            cont,
            args,
            term,
            body,
        } => Term::LetFun {
            name,
            cont,
            args,
            term,
            body: Box::new(propagate_values_(*body, map)),
        },
        Term::LetCnt {
            name,
            args,
            term,
            body,
        } => Term::LetCnt {
            name,
            args,
            term,
            body: Box::new(propagate_values_(*body, map)),
        },
        Term::AppCnt { name, args } => todo!(),
        Term::AppFun { name, cont, args } => todo!(),
        Term::IfElse { cond, then, or } => todo!(),
        Term::SetThen { name, value, body } => todo!(),
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn app() {
        let res = cps(
            ML::app(ML::var("f"), &[ML::Bool(true), ML::Bool(false)]),
            Box::new(|x| Term::Var(x)),
        );
        println!("{res}");
        let res = kps(
            ML::app(ML::var("f"), &[ML::Bool(true), ML::Bool(false)]),
            "return".into(),
        );
        println!("{res}");
    }

    #[test]
    fn multiple_args() {
        let res = cps(
            ML::app(ML::var("f"), &[ML::Bool(true), ML::var("y")]),
            Box::new(|x| Term::Var(x)),
        );
        println!("{res}");
        let res = kps(
            ML::app(ML::var("f"), &[ML::Bool(true), ML::var("y")]),
            "return".into(),
        );
        println!("{res}");
    }

    #[test]
    fn set_under_if() {
        let res = cps(
            ML::seq(&[
                ML::set("x", ML::Bool(true)),
                ML::if_then_else(
                    ML::var("flag"),
                    ML::set("x", ML::Bool(true)),
                    ML::set("x", ML::Bool(false)),
                ),
                ML::app(ML::var("or"), &[ML::var("x"), ML::var("x")]),
            ]),
            Box::new(|x| Term::Var(x)),
        );
        println!("{}", res.to_cxx(0))
    }

    #[test]
    fn set_app() {
        let res = cps(
            ML::seq(&[
                ML::set("x", ML::Bool(true)),
                ML::app(ML::var("or"), &[ML::var("x"), ML::var("x")]),
            ]),
            Box::new(|x| Term::Var(x)),
        );
        println!("{res}")
    }

    #[test]
    fn set() {
        let res = cps(ML::set("x", ML::Bool(true)), Box::new(|x| Term::Var(x)));
        println!("{res}");
        let res = kps(ML::set("x", ML::Bool(true)), "return".into());
        println!("{res}");
    }

    #[test]
    fn seq() {
        let res = cps(
            ML::seq(&[
                ML::set("x", ML::Bool(true)),
                ML::app(ML::var("f"), &[ML::var("x")]),
            ]),
            Box::new(|x| Term::Var(x)),
        );
        println!("{res}");
    }

    #[test]
    fn letv() {
        let res = cps(
            ML::val(
                "x".to_string(),
                ML::app(ML::var("+"), &[ML::real("21"), ML::real("21")]),
                ML::var("x"),
            ),
            Box::new(|x| Term::Var(x)),
        );
        println!("{res}");
    }

    #[test]
    fn if_under_if() {
        let res = cps(
            ML::if_then_else(
                ML::var("a"),
                ML::if_then_else(ML::var("b"), ML::var("x"), ML::var("y")),
                ML::var("z"),
            ),
            Box::new(|x| Term::Var(x)),
        );
        println!("{res}");
    }
}
