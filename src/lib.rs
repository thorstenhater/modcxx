pub mod ann;
pub mod arb;
pub mod ast;
pub mod cps;
pub mod cxx;
pub mod dif;
pub mod err;
pub mod exp;
pub mod lex;
pub mod loc;
pub mod nmd;
pub mod ode;
pub mod opt;
pub mod par;
pub mod src;
pub mod usr;

use std::collections::BTreeMap;
use std::collections::BTreeSet;

type Set<T> = BTreeSet<T>;
type Map<K, V> = BTreeMap<K, V>;
