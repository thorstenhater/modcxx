pub mod ann;
pub mod arb;
pub mod ast;
pub mod cps;
pub mod cxx;
pub mod err;
pub mod exp;
pub mod lex;
pub mod loc;
pub mod nmd;
pub mod opt;
pub mod par;
pub mod src;
pub mod usr;
pub mod ode;
pub mod alg;
pub mod grp;

use std::collections::BTreeMap;
use std::collections::BTreeSet;

type Set<T> = BTreeSet<T>;
type Map<K, V> = BTreeMap<K, V>;
