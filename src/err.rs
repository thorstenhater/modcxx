use crate::lex::Type;
use crate::src::Location;
use thiserror::Error;

pub type Result<T> = std::result::Result<T, ModcxxError>;

#[derive(Debug, Error, PartialEq, Eq)]
pub enum ModcxxError {
    #[error("In line {0:?}: unexpected token {1:?} ({2:?}), allowed here {3:?}.")]
    UnexpectedToken(Location, Type, Option<String>, Vec<Type>),
    #[error("In {0:?}: Illegal ionic quantity {1}, must start or end with {2}.")]
    IllegalIonic(Location, String, String),
    #[error("Module has no {0} block, which is required.")]
    MissingBlock(String),
    #[error("Module has no kind, which is required; specify one of SUFFIX, POINT_PROCESS....")]
    MissingKind,
    #[error("Cannot arborize NMODL: feature {0} is not supported in Arbor.")]
    ArborUnsupported(String),
    #[error("Cannot create module; feature {0} is not supported in Arbor.\n{1}")]
    Unsupported(String, String),
    #[error("Duplicate symbol {0} in {1:?}, first defined here {2:?}.")]
    DuplicateSymbol(String, Location, Location),
    #[error("Duplicate block {0} in {1:?}, first defined here {2:?}.")]
    DuplicateBlock(String, Location, Location),
    #[error("Duplicate title {0} in {1:?}, first defined as {2} here {3:?}.")]
    DuplicateTitle(String, Location, String, Location),
    #[error("Duplicate NMODL kind {0} here {1:?}, first defined as {2} here {3:?}.")]
    DuplicateKind(String, Location, String, Location),
    #[error("Used reserved name {0} here {1:?}.")]
    ReservedWord(String, Location),
    #[error("Use of unbound name {0} here {1:?}.")]
    UnboundName(String, Location),
    #[error("Writing to read-only variable {0} here {1:?}.")]
    WriteToRO(String, Location),
    #[error("Symbol {0} is callable, used as a variable here {1:?}.")]
    CallableNotVariable(String, Location),
    #[error("Symbol {0} is variable, used as a callable here {1:?}.")]
    VariableNotCallable(String, Location),
    #[error("Internal Error {0}.")]
    InternalError(String),
}
