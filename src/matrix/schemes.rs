//! Implementation of dependency schemes
//!
//! A dependency scheme allows to detect pseudo-dependencies in a quantified formula.
//! We currently implement the ``Reflexive resolution-path dependency scheme'' [1] which is sound for QBF and DQBF [2].
//!
//! [1] ``Soundness of Q-resolution with dependency schemes'' by Slivovsky and Szeider
//! [2] ``Dependency Schemes for DQBF'' by Wimmer et al.

use crate::{
    literal::{Literal, Variable},
    matrix::{Matrix, Prefix, VariableInfo},
};
use log::{debug, trace};
use rustc_hash::FxHashSet;

impl<P: Prefix> Matrix<P> {
    pub(crate) fn refl_res_path_dep_scheme(&mut self) -> usize {
        trace!("refl_res_path_dep_scheme");
        let mut removed = 0;
        let mut seen_pos: FxHashSet<Literal> = FxHashSet::default();
        let mut seen_neg: FxHashSet<Literal> = FxHashSet::default();
        for var in 1..=self.prefix.variables().max_variable_id() {
            let var: Variable = var.into();
            let info = self.prefix.variables().get(var);
            if !info.is_universal() {
                continue;
            }
            debug_assert!(info.is_bound());

            seen_neg.clear();
            seen_pos.clear();

            self.search_resolution_path(Literal::new(var, false), &mut seen_pos);
            self.search_resolution_path(Literal::new(var, true), &mut seen_neg);

            for e_var in 1..=self.prefix.variables().max_variable_id() {
                let e_var: Variable = e_var.into();
                let info = self.prefix.variables().get(e_var);
                if info.is_universal() {
                    continue;
                }
                if !self.prefix.depends_on(e_var, var) {
                    continue;
                }

                let pos = Literal::new(e_var, false);
                let neg = Literal::new(e_var, true);

                if (!seen_pos.contains(&pos) || !seen_neg.contains(&pos))
                    || (!seen_neg.contains(&pos) && !seen_pos.contains(&neg))
                {
                    self.prefix.mut_vars().get_mut(e_var).remove_dependency(var);
                    debug!("detected spurious dependency {} of {}", var, e_var);
                    removed += 1;
                }
            }
        }
        removed
    }

    fn search_resolution_path(&self, root: Literal, seen: &mut FxHashSet<Literal>) {
        let mut stack = Vec::new();
        for &clause_id in self.occurrences(root) {
            let clause = &self.clauses[clause_id as usize];
            for literal in clause.iter() {
                if seen.contains(literal) {
                    continue;
                }
                seen.insert(*literal);
                let info = self.prefix.variables().get(literal.variable());
                if info.is_universal() {
                    continue;
                }
                if !self.prefix.depends_on(literal.variable(), root.variable()) {
                    continue;
                }
                stack.push(literal);
            }
        }
        while let Some(&lit) = stack.pop() {
            let lit = -lit;
            for &clause_id in self.occurrences(lit) {
                let clause = &self.clauses[clause_id as usize];
                for literal in clause.iter() {
                    if seen.contains(literal) {
                        continue;
                    }
                    seen.insert(*literal);
                    let info = self.prefix.variables().get(literal.variable());
                    if info.is_universal() {
                        continue;
                    }
                    if !self.prefix.depends_on(literal.variable(), root.variable()) {
                        continue;
                    }
                    stack.push(literal);
                }
            }
        }
        //dbg!(seen);
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::parse::qdimacs;

    #[test]
    fn test_dep_scheme() {
        let instance = "c
c reflexive resolution path dependency should be able to eliminate 4 from 2 and 3 accoding to Example 2 of ``Soundness of Q-resolution with dependency schemes''
p cnf 4 4
e 1 0
a 4 0
e 2 3 0
4 2 0
-4 3 0
1 -3 0
-1 -2 0
";
        let mut matrix = qdimacs::parse(&instance).unwrap();
        matrix.refl_res_path_dep_scheme();

        assert!(!matrix.prefix.depends_on(2_u32, 4_u32));
        assert!(!matrix.prefix.depends_on(3_u32, 4_u32));
    }
}
