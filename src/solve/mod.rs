use super::dimacs::Dimacs;
use serde::{Deserialize, Serialize};

pub mod caqe;
pub mod dcaqe;

#[derive(Debug, PartialEq, Eq, Copy, Clone, Serialize, Deserialize)]
pub enum SolverResult {
    Satisfiable = 10,
    Unsatisfiable = 20,
    Unknown = 30,
}

impl Dimacs for SolverResult {
    fn dimacs(&self) -> String {
        match *self {
            SolverResult::Satisfiable => String::from("1"),
            SolverResult::Unsatisfiable => String::from("0"),
            SolverResult::Unknown => String::from("-1"),
        }
    }
}

pub trait Solver {
    fn solve(&mut self) -> SolverResult;
}
