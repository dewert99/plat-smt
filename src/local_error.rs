use crate::Sort;

#[derive(Debug)]
pub enum LocalError {
    SortMismatch { actual: Sort, expected: Sort },
    Unsupported(&'static str),
}

pub type Result<T> = core::result::Result<T, LocalError>;
pub type IResult<T> = core::result::Result<T, (LocalError, usize)>;
