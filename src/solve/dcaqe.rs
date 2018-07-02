extern crate cryptominisat;
use self::cryptominisat::*;

extern crate bit_vec;
use self::bit_vec::BitVec;

use super::super::*;

#[cfg(feature = "statistics")]
use super::super::utils::statistics::TimingStats;

use super::super::parse::dqdimacs;

use super::super::matrix::depenendcy::*;

type DQMatrix = Matrix<DependencyPrefix>;

pub struct DCaqeSolver<'a> {
    matrix: &'a DQMatrix,
    result: SolverResult,
}
