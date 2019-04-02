use super::matrix::hierarchical::*;
use super::*;
use rustc_hash::FxHashMap;

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Clause {
    literals: Vec<Literal>,
}

impl Clause {
    /// Creates a new clause from given literals
    ///
    /// The vector containing literals is sorted and deduplicated.
    pub fn new(literals: Vec<Literal>) -> Self {
        let mut l = literals;
        l.sort();
        l.dedup();
        Self::new_normalized(l)
    }

    /// Creates an empty clause
    pub fn new_empty() -> Self {
        Self {
            literals: Vec::new(),
        }
    }

    /// Creates a new clause from given literals
    ///
    /// Assumes literals to be already normalized, i.e.,
    /// sorted and without duplication.
    pub fn new_normalized(literals: Vec<Literal>) -> Self {
        Self { literals }
    }

    pub fn len(&self) -> usize {
        self.literals.len()
    }

    pub fn is_tautology(&self) -> bool {
        for (i, &el1) in self.literals.iter().enumerate() {
            if i + 1 >= self.literals.len() {
                break;
            }
            let el2 = self.literals[i + 1];
            if el1 == -el2 {
                return true;
            }
        }
        true
    }

    pub fn reduce_universal_qbf(&mut self, prefix: &HierarchicalPrefix) {
        let max = self
            .literals
            .iter()
            .filter(|l| !prefix.variables().get(l.variable()).is_universal())
            .fold(0, |max, l| {
                let level = prefix.variables().get(l.variable()).level;
                if level > max {
                    level
                } else {
                    max
                }
            });
        self.literals.retain(|l| {
            let info = prefix.variables().get(l.variable());
            !info.is_universal() || info.level < max
        });
    }

    pub fn iter(&self) -> std::slice::Iter<Literal> {
        self.literals.iter()
    }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<Literal> {
        self.literals.iter_mut()
    }

    pub fn retain<P>(&mut self, predicate: P)
    where
        P: FnMut(&Literal) -> bool,
    {
        self.literals.retain(predicate);
    }

    /// Returns true, if the literals contained in `self` are a subset of the literals in `other`.
    /// Only literals satisfying the predicate are considered.
    /// Note that literals in clauses are sorted.
    pub fn is_subset_wrt_predicate<P>(&self, other: &Self, predicate: P) -> bool
    where
        P: Fn(&Literal) -> bool,
    {
        // iterate over all literals in lhs and try to match it to the literals in rhs
        let mut lhs = self.iter().filter(|l| predicate(l));
        let mut rhs = other.iter().filter(|l| predicate(l));
        let mut rhs_literal = match rhs.next() {
            None => {
                // check that there are no remaining literals in lhs
                return lhs.next().is_none();
            }
            Some(l) => l,
        };
        while let Some(lhs_literal) = lhs.next() {
            if lhs_literal < rhs_literal {
                // have not found a matching literal in rhs
                return false;
            }
            debug_assert!(lhs_literal >= rhs_literal);
            while lhs_literal > rhs_literal {
                rhs_literal = match rhs.next() {
                    None => return false,
                    Some(l) => l,
                }
            }
            if lhs_literal == rhs_literal {
                // same literal, proceed with both
                rhs_literal = match rhs.next() {
                    None => {
                        // check that there are no remaining literals in lhs
                        return lhs.next().is_none();
                    }
                    Some(l) => l,
                };
                continue;
            } else {
                return false;
            }
        }
        true
    }

    pub fn is_subset(&self, other: &Self) -> bool {
        self.is_subset_wrt_predicate(other, |_| true)
    }

    /// Returns true, if the literals contained in `self` are equal to the literals in `other`.
    /// Only literals satisfying the predicate are considered.
    /// Note that literals in clauses are sorted.
    pub fn is_equal_wrt_predicate<P>(&self, other: &Self, predicate: P) -> bool
    where
        P: Fn(&Literal) -> bool,
    {
        // iterate over all literals in lhs and try to match it to the literals in rhs
        let mut lhs = self.iter().filter(|l| predicate(l));
        let mut rhs = other.iter().filter(|l| predicate(l));
        loop {
            match (lhs.next(), rhs.next()) {
                (None, None) => return true,
                (Some(l), Some(r)) => {
                    if l != r {
                        return false;
                    }
                }
                (_, _) => return false,
            }
        }
    }

    pub fn is_equal(&self, other: &Self) -> bool {
        self.is_equal_wrt_predicate(other, |_| true)
    }

    pub fn is_satisfied_by_assignment(&self, assignment: &FxHashMap<Variable, bool>) -> bool {
        self.literals
            .iter()
            .any(|&l| match assignment.get(&l.variable()) {
                None => false,
                Some(&value) => l.signed() && !value || !l.signed() && value,
            })
    }
}

impl Dimacs for Clause {
    fn dimacs(&self) -> String {
        let mut dimacs = String::new();
        for &literal in self.iter() {
            dimacs.push_str(&format!("{} ", literal.dimacs()));
        }
        dimacs.push_str("0");
        dimacs
    }
}

#[cfg(test)]
mod tests {
    use std::mem;

    use super::*;

    #[test]
    fn size_of_clause() {
        let result = mem::size_of::<Clause>();
        assert!(
            result == 24,
            "Size of `Clause` should be 24 bytes, was `{}`",
            result
        );
    }

    #[test]
    fn clause_normalization() {
        let lit1 = Literal::new(0_u32, false);
        let lit2 = Literal::new(1u32, false);
        let literals = vec![lit2, lit1, lit2];
        let clause1 = Clause::new(literals);
        let clause2 = Clause::new_normalized(vec![lit1, lit2]);
        assert_eq!(clause1, clause2);
    }

    #[test]
    fn clause_reduce_universal_qbf() {
        // cretate a qbf prefix
        let mut prefix = HierarchicalPrefix::new(3);
        let exists1 = prefix.new_scope(ScopeId::OUTERMOST, Quantifier::Existential);
        let forall = prefix.new_scope(exists1, Quantifier::Universal);
        let exists2 = prefix.new_scope(forall, Quantifier::Existential);

        prefix.add_variable(1u32, exists1);
        prefix.add_variable(2u32, forall);
        prefix.add_variable(3u32, exists2);

        let lit1 = Literal::new(1u32, false);
        let lit2 = Literal::new(2u32, false);
        let lit3 = Literal::new(3u32, false);

        // no universal reduction
        let mut clause1 = Clause::new(vec![lit1, lit2, lit3]);
        clause1.reduce_universal_qbf(&prefix);
        let clause2 = Clause::new(vec![lit1, lit2, lit3]);
        assert_eq!(clause1, clause2);

        // lit2 can be removed
        let mut clause1 = Clause::new(vec![lit1, lit2]);
        clause1.reduce_universal_qbf(&prefix);
        let clause2 = Clause::new(vec![lit1]);
        assert_eq!(clause1, clause2);
    }

    #[test]
    fn clause_subset_wrt_predicate() {
        let lit1 = Literal::new(0_u32, false);
        let lit2 = Literal::new(1u32, false);
        let lit3 = Literal::new(2u32, false);
        let clause1 = Clause::new(vec![lit1, -lit2, lit3]);
        let clause2 = Clause::new(vec![lit1, lit2, lit3]);
        assert!(!clause1.is_subset(&clause2));
        assert!(clause1.is_subset_wrt_predicate(&clause2, |l| !l.signed()));
    }

    #[test]
    fn clause_equal_wrt_predicate() {
        let lit1 = Literal::new(0_u32, false);
        let lit2 = Literal::new(1u32, false);
        let lit3 = Literal::new(2u32, false);
        let clause1 = Clause::new(vec![lit1, -lit2, lit3]);
        let clause2 = Clause::new(vec![lit1, lit3]);
        assert!(!clause1.is_equal(&clause2));
        assert!(clause1.is_equal_wrt_predicate(&clause2, |l| !l.signed()));
    }

    #[test]
    fn clause_is_satisifed() {
        let lit1 = Literal::new(0_u32, false);
        let lit2 = Literal::new(1u32, false);
        let lit3 = Literal::new(2u32, false);
        let clause = Clause::new(vec![lit1, -lit2, lit3]);
        let mut assignment: FxHashMap<Variable, bool> = FxHashMap::default();
        assignment.insert(1u32.into(), true);
        assignment.insert(2u32.into(), false);
        assert!(!clause.is_satisfied_by_assignment(&assignment));
        assignment.insert(0_u32.into(), true);
        assert!(clause.is_satisfied_by_assignment(&assignment));
        assignment.insert(0_u32.into(), false);
        assert!(!clause.is_satisfied_by_assignment(&assignment));
    }

    #[test]
    fn clause_dimacs() {
        let lit1 = Literal::new(1u32, false);
        let lit2 = Literal::new(2u32, false);
        let lit3 = Literal::new(3u32, false);
        let clause = Clause::new(vec![lit1, -lit2, lit3]);
        assert_eq!(clause.dimacs(), "1 -2 3 0");
    }

}
