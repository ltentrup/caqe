use super::dimacs::Dimacs;
use serde::{Deserialize, Serialize};

pub mod caqe;
#[cfg(dcaqe)]
pub mod dcaqe;

#[derive(Debug, PartialEq, Eq, Copy, Clone, Serialize, Deserialize)]
pub enum SolverResult {
    Satisfiable = 10,
    Unsatisfiable = 20,
    Unknown = 30,
}

impl Dimacs for SolverResult {
    #[must_use]
    fn dimacs(&self) -> String {
        match *self {
            Self::Satisfiable => String::from("1"),
            Self::Unsatisfiable => String::from("0"),
            Self::Unknown => String::from("-1"),
        }
    }
}

pub trait Solver {
    fn solve(&mut self) -> SolverResult;
}
