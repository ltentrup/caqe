use super::*;

#[derive(PartialEq, Eq, Debug)]
pub struct Clause {
    literals: Vec<Literal>,
}

impl Clause {
    /// Creates a new clause from given literals
    ///
    /// The vector containing literals is sorted and deduplicated.
    pub fn new(literals: Vec<Literal>) -> Clause {
        let mut l = literals;
        l.sort();
        l.dedup();
        Self::new_normalized(l)
    }

    /// Creates a new clause from given literals
    ///
    /// Assumes literals to be already normalized, i.e.,
    /// sorted and without duplication.
    pub fn new_normalized(literals: Vec<Literal>) -> Clause {
        Clause { literals: literals }
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
        let max = self.literals
            .iter()
            .filter(|l| !prefix.get(l.variable()).is_universal)
            .fold(0, |max, l| {
                let level = prefix.get(l.variable()).scope;
                if level > max {
                    level
                } else {
                    max
                }
            });
        self.literals.retain(|l| {
            let info = prefix.get(l.variable());
            !info.is_universal || info.scope < max
        });
    }

    pub fn iter(&self) -> std::slice::Iter<Literal> {
        self.literals.iter()
    }

    /// Returns true, if the literals contained in `self` are a subset of the literals in `other`.
    /// Only literals satisfying the predicate are considered.
    /// Note that literals in clauses are sorted.
    pub fn is_subset_wrt_predicate<P>(&self, other: &Clause, predicate: P) -> bool
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

    pub fn is_subset(&self, other: &Clause) -> bool {
        self.is_subset_wrt_predicate(other, |_| true)
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
        let lit1 = Literal::new(0, false);
        let lit2 = Literal::new(1, false);
        let literals = vec![lit2, lit1, lit2];
        let clause1 = Clause::new(literals);
        let clause2 = Clause::new_normalized(vec![lit1, lit2]);
        assert_eq!(clause1, clause2);
    }

    #[test]
    fn clause_reduce_universal_qbf() {
        // cretate a qbf prefix
        let mut prefix = HierarchicalPrefix::new(3);
        let exists1 = prefix.new_scope(Quantifier::Existential);
        let forall = prefix.new_scope(Quantifier::Universal);
        let exists2 = prefix.new_scope(Quantifier::Existential);

        prefix.add_variable(1, exists1);
        prefix.add_variable(2, forall);
        prefix.add_variable(3, exists2);

        let lit1 = Literal::new(1, false);
        let lit2 = Literal::new(2, false);
        let lit3 = Literal::new(3, false);

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
        let lit1 = Literal::new(0, false);
        let lit2 = Literal::new(1, false);
        let lit3 = Literal::new(2, false);
        let clause1 = Clause::new(vec![lit1, -lit2, lit3]);
        let clause2 = Clause::new(vec![lit1, lit2, lit3]);
        assert!(!clause1.is_subset(&clause2));
        assert!(clause1.is_subset_wrt_predicate(&clause2, |l| !l.signed()));
    }
}
