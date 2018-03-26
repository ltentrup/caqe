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
}

#[cfg(test)]
mod clause_tests {
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
}
