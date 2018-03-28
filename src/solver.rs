#[derive(Debug, PartialEq, Eq)]
pub enum SolverResult {
    Satisfiable = 10,
    Unsatisfiable = 20,
    Unknown = 30,
}

pub trait Solver {
    fn solve(&mut self) -> SolverResult;
}
