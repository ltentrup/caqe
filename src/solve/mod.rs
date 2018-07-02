pub mod caqe;
pub mod dcaqe;

use super::dimacs::Dimacs;

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum SolverResult {
    Satisfiable = 10,
    Unsatisfiable = 20,
    Unknown = 30,
}

impl Dimacs for SolverResult {
    fn dimacs(&self) -> String {
        match self {
            &SolverResult::Satisfiable => String::from("1"),
            &SolverResult::Unsatisfiable => String::from("0"),
            &SolverResult::Unknown => String::from("-1"),
        }
    }
}

pub trait Solver {
    fn solve(&mut self) -> SolverResult;
}
