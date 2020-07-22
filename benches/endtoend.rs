#![feature(test)]

extern crate test;

mod instances;

use caqe::{dimacs::Dimacs, parse::qdimacs, CaqeSolver, Solver, SolverResult};
use test::Bencher;

#[bench]
fn endtoend_bench_arbiter_05_comp_error01_qbf_hardness_depth_8_qdimacs(b: &mut Bencher) {
    b.iter(|| {
        let instance = &instances::ARBITER_05_COMP_ERROR01_QBF_HARDNESS_DEPTH_8_QDIMACS;
        let mut matrix = qdimacs::parse(instance).unwrap();
        matrix.unprenex_by_miniscoping();
        let mut solver = CaqeSolver::new(&mut matrix);
        assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
        assert_eq!(solver.qdimacs_output().dimacs(), "s cnf 0 1056 3040\nV -26 0\nV -31 0\nV -36 0\nV -41 0\nV -46 0\nV -51 0\nV -57 0\nV -63 0\nV -69 0\nV -75 0\n");
    });
}
