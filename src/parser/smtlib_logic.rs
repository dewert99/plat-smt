use core::fmt::{Debug, Formatter};
use core::ops::BitOr;
use core::str::FromStr;

#[derive(Eq, PartialEq, Copy, Clone)]
pub struct SmtlibLogic(u32);

impl BitOr for SmtlibLogic {
    type Output = SmtlibLogic;

    fn bitor(self, rhs: Self) -> Self::Output {
        self.combine(rhs)
    }
}

impl SmtlibLogic {
    pub const fn combine(self, rhs: SmtlibLogic) -> SmtlibLogic {
        SmtlibLogic(self.0 | rhs.0)
    }

    pub const CORE: Self = SmtlibLogic(0);
    pub const QF_UF: Self = SmtlibLogic(1 << 0);

    const RATIONAL: Self = SmtlibLogic(1 << 1);

    const LINEAR_ARITH: Self = SmtlibLogic(1 << 2);
    pub const QF_LRA: Self = Self::RATIONAL.combine(Self::LINEAR_ARITH);
    pub const QF_UFLRA: Self = Self::QF_UF.combine(Self::QF_LRA);

    pub fn to_str(self) -> &'static str {
        match self {
            Self::CORE => "Core",
            Self::QF_UF => "QF_UF",
            Self::QF_LRA => "QF_LRA",
            Self::QF_UFLRA => "QF_UFLRA(incomplete)",
            _ => "???",
        }
    }

    pub fn supports(self, oth: Self) -> bool {
        self | oth == self
    }
}

impl Default for SmtlibLogic {
    fn default() -> Self {
        Self::CORE
    }
}

impl Debug for SmtlibLogic {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        let s = self.to_str();
        if s == "???" {
            writeln!(f, "SmtlibLogic({})", self.0)
        } else {
            f.write_str(s)
        }
    }
}

impl FromStr for SmtlibLogic {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "Core" => Ok(Self::CORE),
            "QF_UF" => Ok(Self::QF_UF),
            "QF_LRA" => Ok(Self::QF_LRA),
            _ => Err(()),
        }
    }
}
