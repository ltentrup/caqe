use super::*;
use bit_vec::BitVec;
use rustc_hash::FxHashMap;

pub mod depenendcy;
pub mod hierarchical;
mod schemes;

pub type ClauseId = u32;

pub trait Prefix {
    type V: VariableInfo;

    fn new(num_variables: usize) -> Self;

    fn variables(&self) -> &VariableStore<Self::V>;

    /// This function is called in `Matrix::add` for every literal in clause
    fn import(&mut self, variable: Variable);

    /// Reduces a clause universally
    fn reduce_universal(&self, clause: &mut Clause);

    /// Checks if an existential variable `var` depends on `other`.
    fn depends_on<V: Into<Variable>, U: Into<Variable>>(&self, var: V, other: U) -> bool;
}

#[derive(Debug)]
pub struct Matrix<P: Prefix> {
    pub prefix: P,
    pub clauses: Vec<Clause>,
    occurrences: FxHashMap<Literal, Vec<ClauseId>>,
    conflict: bool,
    pub orig_clause_num: usize,
}

impl<P: Prefix> Matrix<P> {
    pub fn new(num_variables: usize, num_clauses: usize) -> Matrix<P> {
        Matrix {
            prefix: P::new(num_variables),
            clauses: Vec::with_capacity(num_clauses),
            occurrences: FxHashMap::default(),
            conflict: false,
            orig_clause_num: num_clauses,
        }
    }

    /// Adds a clause to the matrix and returns its `ClauseId`
    pub fn add(&mut self, mut clause: Clause) -> ClauseId {
        self.prefix.reduce_universal(&mut clause);
        for &literal in clause.iter() {
            let occurrences = self.occurrences.entry(literal).or_insert_with(Vec::new);
            occurrences.push(self.clauses.len() as ClauseId);
            self.prefix.import(literal.variable());
        }
        if clause.len() == 0 {
            self.conflict = true;
        }
        self.clauses.push(clause);
        (self.clauses.len() - 1) as ClauseId
    }

    pub fn occurrences(&self, literal: Literal) -> std::slice::Iter<ClauseId> {
        match self.occurrences.get(&literal) {
            None => [].iter(),
            Some(vec) => vec.iter(),
        }
    }

    pub fn conflict(&self) -> bool {
        self.conflict
    }
}

impl<P: Prefix> Dimacs for Matrix<P>
where
    P: Dimacs,
{
    fn dimacs(&self) -> String {
        let mut dimacs = String::new();
        dimacs.push_str(&format!(
            "p cnf {} {}\n",
            self.prefix.variables().num_variables(),
            self.clauses.len()
        ));
        dimacs.push_str(&self.prefix.dimacs().to_string());
        for clause in self.clauses.iter() {
            dimacs.push_str(&format!("{}\n", clause.dimacs()));
        }

        dimacs
    }
}

pub trait VariableInfo: std::clone::Clone + std::fmt::Debug {
    fn new() -> Self;
    fn is_universal(&self) -> bool;
    fn is_bound(&self) -> bool;

    fn is_existential(&self) -> bool {
        !self.is_universal()
    }
}

#[derive(Debug)]
pub struct VariableStore<V: VariableInfo> {
    variables: Vec<V>,
    used: BitVec,
    orig_num_variables: usize,
    unbounded: V,
}

impl<V: VariableInfo> VariableStore<V> {
    pub fn new(num_variables: usize) -> Self {
        let mut variables = Vec::with_capacity(num_variables + 1);
        variables.push(V::new());

        let mut used = BitVec::with_capacity(num_variables + 1);
        used.grow(num_variables + 1, false);
        used.set(0, true);

        VariableStore {
            variables: variables,
            used,
            orig_num_variables: num_variables,
            unbounded: V::new(),
        }
    }

    pub fn get(&self, variable: Variable) -> &V {
        let index: usize = variable.into();
        if index >= self.variables.len() {
            // variable was not bound prior
            return &self.unbounded;
        }
        &self.variables[index]
    }

    pub fn num_variables(&self) -> usize {
        assert!(self.variables.len() > 0);
        self.variables.len() - 1
    }

    pub fn orig_num_variables(&self) -> usize {
        self.orig_num_variables
    }

    /// Makes sure variable vector is large enough
    /// Also, marks the variable as `used`
    fn import(&mut self, variable: Variable) {
        let index: usize = variable.into();
        if self.variables.len() <= index {
            self.variables.resize(index + 1, V::new())
        }
        if self.used.len() <= index {
            self.used.grow(index + 1, false);
        }
        self.used.set(index, true);
    }

    fn get_mut(&mut self, variable: Variable) -> &mut V {
        let index: usize = variable.into();
        assert!(index < self.variables.len());
        &mut self.variables[index]
    }

    /// Returns the next unused variable
    pub fn next_unused(&self) -> Variable {
        if let Some((index, _)) = self.used.iter().enumerate().filter(|(_, val)| !val).next() {
            index.into()
        } else {
            self.used.len().into()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_matrix_occurrences() {
        let instance = "c
p cnf 4 4
a 1 2 0
e 3 4 0
1 3 0
-1 4 0
-3 -4 0
1 2 4 0
";
        let lit1 = Literal::new(1u32, false);
        let lit2 = Literal::new(2u32, false);
        let lit3 = Literal::new(3u32, false);
        let lit4 = Literal::new(4u32, false);
        let matrix = parse::qdimacs::parse(&instance).unwrap();
        assert_eq!(matrix.occurrences(lit1).len(), 2);
        assert_eq!(matrix.occurrences(-lit1).len(), 1);
        assert_eq!(matrix.occurrences(lit2).len(), 1);
        assert_eq!(matrix.occurrences(-lit2).len(), 0);
        assert_eq!(matrix.occurrences(lit3).len(), 1);
        assert_eq!(matrix.occurrences(-lit3).len(), 1);
        assert_eq!(matrix.occurrences(lit4).len(), 2);
        assert_eq!(matrix.occurrences(-lit4).len(), 1);
        assert!(matrix.prefix.depends_on(lit3.variable(), lit1.variable()));
    }

    #[test]
    fn test_matrix_dimacs() {
        let instance = "p cnf 4 4
a 1 2 0
e 3 4 0
1 3 0
-1 4 0
-3 -4 0
1 2 4 0
";
        let matrix = parse::qdimacs::parse(&instance).unwrap();
        let dimacs = matrix.dimacs();
        assert_eq!(instance, dimacs);
    }

    #[test]
    fn test_partitioning() {
        let instance = "c
p cnf 10 8
a 1 2 0
e 3 4 0
a 5 6 0
e 7 8 9 10 0
-1 3 9 0
1 -3 9 0
-9 -5 7 0
-9 5 -7 0
-2 4 10 0
2 -4 10 0
-10 -6 8 0
-10 6 -8 0
";
        let mut matrix = parse::qdimacs::parse(&instance).unwrap();
        matrix.unprenex_by_miniscoping(false);
        assert!(matrix.prefix.roots.len() == 2);
    }

    #[test]
    fn test_matrix_dimacs_tree() {
        let instance = "p cnf 4 4
a 1 2 0
e 3 4 0
1 3 0
-1 4 0
-3 -4 0
1 2 4 0
";
        let mut matrix = parse::qdimacs::parse(&instance).unwrap();
        matrix.unprenex_by_miniscoping(false);
        let dimacs = matrix.dimacs();
        assert_eq!(instance, dimacs);
    }

}
