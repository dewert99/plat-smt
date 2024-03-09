use crate::util::display_debug;
use egg::Symbol;
use internment::Intern;
use std::fmt::{Debug, Formatter};

pub type Sort = Intern<BaseSort>;

#[derive(Hash, Eq, PartialEq)]
pub struct BaseSort {
    pub name: Symbol,
    pub params: Box<[Sort]>,
}

impl Debug for BaseSort {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.params.len() == 0 {
            write!(f, "{}", self.name)
        } else {
            write!(f, "({}", self.name)?;
            for x in &*self.params {
                write!(f, " {x}")?;
            }
            write!(f, ")")
        }
    }
}

display_debug!(BaseSort);
