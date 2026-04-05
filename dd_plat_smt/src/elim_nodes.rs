use crate::use_mutator::{HandleResult, Mutator};
use plat_smt::parser::{SexpTerminal, SexpToken};

#[derive(Debug)]
pub struct ElimNodes;

pub enum ElimNodesParentInfo {
    Assert,
    Assoc,
    Other,
}

impl Mutator for ElimNodes {
    type AncestorInfo = ElimNodesParentInfo;

    fn from_data(_: &str) -> Self {
        ElimNodes
    }

    fn describe_parent(&self, parent: &str, _: Option<&Self::AncestorInfo>) -> Self::AncestorInfo {
        match parent {
            "assert" => ElimNodesParentInfo::Assert,
            "or" | "and" | "distinct" => ElimNodesParentInfo::Assoc,
            _ => ElimNodesParentInfo::Other,
        }
    }

    fn handle(
        &mut self,
        parent_info: &Self::AncestorInfo,
        child: &SexpToken<'_, &str>,
        skip_first: &mut bool,
    ) -> Option<HandleResult<'static>> {
        if *skip_first {
            return None;
        }
        match parent_info {
            ElimNodesParentInfo::Assert => match child {
                SexpToken::Terminal(SexpTerminal::Symbol("true")) => None,
                _ => Some(HandleResult::ReplaceWithConst("true")),
            },
            ElimNodesParentInfo::Assoc => Some(HandleResult::Remove),
            ElimNodesParentInfo::Other => None,
        }
    }
}
