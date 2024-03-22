use crate::{
    err::{ModcxxError, Result},
    loc::Location,
    Map,
};

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Metadata {
    Location(Location),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Default)]
pub struct Annotation {
    data: Map<String, Metadata>,
}

impl Annotation {
    pub fn add_loc(&mut self, loc: Location) {
        self.data
            .insert("location".to_string(), Metadata::Location(loc));
    }

    pub fn add_end(&mut self, loc: Location) {
        self.data.insert("end".to_string(), Metadata::Location(loc));
    }

    pub fn get_loc(&self) -> Result<Location> {
        if let Some(Metadata::Location(l)) = self.data.get("location") {
            Ok(*l)
        } else {
            Err(ModcxxError::InternalError(String::from(
                "No location defined in metadata.",
            )))
        }
    }
}
