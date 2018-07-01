use super::*;

pub mod depenendcy;
pub mod hierarchical;

pub type ClauseId = u32;

pub trait Prefix {
    type V: VariableInfo;

    fn new(num_variables: usize) -> Self;

    fn variables(&self) -> &VariableStore<Self::V>;

    /// This function is called in `Matrix::add` for every literal in clause
    fn import(&mut self, variable: Variable);

    /// Reduces a clause universally
    fn reduce_universal(&self, clause: &mut Clause);
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

    pub fn add(&mut self, mut clause: Clause) {
        self.prefix.reduce_universal(&mut clause);
        for &literal in clause.iter() {
            let occurrences = self.occurrences.entry(literal).or_insert(Vec::new());
            occurrences.push(self.clauses.len() as ClauseId);
            self.prefix.import(literal.variable());
        }
        if clause.len() == 0 {
            self.conflict = true;
        }
        self.clauses.push(clause);
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
        dimacs.push_str(&format!("{}", self.prefix.dimacs()));
        for ref clause in self.clauses.iter() {
            dimacs.push_str(&format!("{}\n", clause.dimacs()));
        }

        dimacs
    }
}

pub trait VariableInfo: std::clone::Clone {
    fn new() -> Self;
}

#[derive(Debug)]
pub struct VariableStore<V: VariableInfo> {
    variables: Vec<V>,
    orig_num_variables: usize,
    unbounded: V,
}

impl<V: VariableInfo> VariableStore<V> {
    pub fn new(num_variables: usize) -> Self {
        let mut variables = Vec::with_capacity(num_variables + 1);
        variables.push(V::new());
        VariableStore {
            variables: variables,
            orig_num_variables: num_variables,
            unbounded: V::new(),
        }
    }

    pub fn get(&self, variable: Variable) -> &V {
        let index = variable as usize;
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
    fn import(&mut self, variable: Variable) {
        if self.variables.len() <= variable as usize {
            self.variables.resize((variable + 1) as usize, V::new())
        }
    }

    fn get_mut(&mut self, variable: Variable) -> &mut V {
        let index = variable as usize;
        assert!(index < self.variables.len());
        &mut self.variables[index]
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
        let lit1 = Literal::new(1, false);
        let lit2 = Literal::new(2, false);
        let lit3 = Literal::new(3, false);
        let lit4 = Literal::new(4, false);
        let matrix = parsing::qdimacs::parse(&instance).unwrap();
        assert_eq!(matrix.occurrences(lit1).len(), 2);
        assert_eq!(matrix.occurrences(-lit1).len(), 1);
        assert_eq!(matrix.occurrences(lit2).len(), 1);
        assert_eq!(matrix.occurrences(-lit2).len(), 0);
        assert_eq!(matrix.occurrences(lit3).len(), 1);
        assert_eq!(matrix.occurrences(-lit3).len(), 1);
        assert_eq!(matrix.occurrences(lit4).len(), 2);
        assert_eq!(matrix.occurrences(-lit4).len(), 1);
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
        let matrix = parsing::qdimacs::parse(&instance).unwrap();
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
        let matrix = parsing::qdimacs::parse(&instance).unwrap();
        let matrix = Matrix::unprenex_by_miniscoping(matrix, false);
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
        let matrix = parsing::qdimacs::parse(&instance).unwrap();
        let matrix = Matrix::unprenex_by_miniscoping(matrix, false);
        let dimacs = matrix.dimacs();
        assert_eq!(instance, dimacs);
    }

}
