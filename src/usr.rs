use crate::{loc::Location, Map};
use std::iter::IntoIterator;

#[derive(Clone, PartialEq, Eq, Debug, Default, Copy)]
pub enum Kind {
    #[default]
    Global,
    Local,
    Argument,
}

#[derive(Clone, PartialEq, Eq, Debug, Default, Copy)]
pub struct Use {
    pub args: usize,
    pub src: Location,
    pub kind: Kind,
}

#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Entry {
    pub reads: Vec<Use>,
    pub writes: Vec<Use>,
    pub solves: Vec<Use>,
    pub calls: Vec<Use>,
}

impl Entry {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn merge(&mut self, other: &Self) {
        self.reads.extend(other.reads.iter().cloned());
        self.writes.extend(other.writes.iter().cloned());
        self.solves.extend(other.solves.iter().cloned());
        self.calls.extend(other.calls.iter().cloned());
    }
}

pub trait Uses {
    fn uses(&self) -> Inventory;
}

#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Inventory(pub Map<String, Entry>);

impl Inventory {
    pub fn merge(&mut self, other: &Self) {
        for (k, v) in other.0.iter() {
            self.0.entry(k.clone()).or_default().merge(v);
        }
    }

    pub fn new() -> Self {
        Self(Map::new())
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn is_read(&self, name: &str) -> Option<Use> {
        self.0.get(name).and_then(|e| e.reads.first().copied())
    }

    pub fn is_read_kind(&self, name: &str, kind: Kind) -> Option<Use> {
        self.0
            .get(name)
            .and_then(|e| e.reads.iter().find(|u| u.kind == kind).copied())
    }

    pub fn is_written(&self, name: &str) -> Option<Use> {
        self.0.get(name).and_then(|e| e.writes.first().copied())
    }

    pub fn is_written_kind(&self, name: &str, kind: Kind) -> Option<Use> {
        self.0
            .get(name)
            .and_then(|e| e.writes.iter().find(|u| u.kind == kind).copied())
    }

    pub fn is_solved(&self, name: &str) -> Option<Use> {
        self.0.get(name).and_then(|e| e.solves.first().copied())
    }

    pub fn is_called(&self, name: &str) -> Option<Use> {
        self.0.get(name).and_then(|e| e.calls.first().copied())
    }

    pub fn is_used(&self, name: &str) -> bool {
        self.is_read(name).is_some()
            || self.is_written(name).is_some()
            || self.is_solved(name).is_some()
            || self.is_called(name).is_some()
    }

    pub fn iter(&self) -> impl Iterator<Item = (&String, &Entry)> {
        self.0.iter()
    }

    pub fn insert(&mut self, name: String, entry: Entry) {
        self.0.insert(name, entry);
    }

    pub fn get(&self, name: &str) -> Option<&Entry> {
        self.0.get(name)
    }
}

impl IntoIterator for Inventory {
    type Item = (String, Entry);

    type IntoIter = <std::collections::BTreeMap<std::string::String, Entry> as std::iter::IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}
