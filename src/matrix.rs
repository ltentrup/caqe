use super::*;

pub trait Prefix {
    fn new(num_variables: usize) -> Self;

    fn num_variables(&self) -> usize;
}

#[derive(Debug)]
pub struct Matrix<P: Prefix> {
    pub prefix: P,
    clauses: Vec<Clause>,
}

impl<P: Prefix> Matrix<P> {
    pub fn new(num_variables: usize, num_clauses: usize) -> Matrix<P> {
        Matrix {
            prefix: P::new(num_variables),
            clauses: Vec::with_capacity(num_clauses),
        }
    }

    pub fn add(&mut self, clause: Clause) {
        self.clauses.push(clause);
    }
}

impl<P: Prefix> Dimacs for Matrix<P> {
    fn dimacs(&self) -> String {
        let mut dimacs = String::new();
        dimacs.push_str(&format!(
            "p cnf {} {}",
            self.prefix.num_variables(),
            self.clauses.len()
        ));
        dimacs
    }
}

pub type ScopeId = i32;

#[derive(Debug, Clone)]
pub struct VariableInfo {
    scope: ScopeId,
    is_universal: bool,
}

impl VariableInfo {
    fn is_bound(&self) -> bool {
        self.scope >= 0
    }
}

#[derive(Debug)]
pub struct Scope {
    variables: Vec<Variable>,
}

impl Scope {
    fn new() -> Scope {
        Scope {
            variables: Vec::new(),
        }
    }
}

#[derive(Debug)]
pub struct HierarchicalPrefix {
    variables: Vec<VariableInfo>,
    scopes: Vec<Scope>,
}

pub enum Quantifier {
    Existential,
    Universal,
}

impl Prefix for HierarchicalPrefix {
    fn new(num_variables: usize) -> Self {
        HierarchicalPrefix {
            variables: Vec::with_capacity(num_variables + 1),
            scopes: vec![
                Scope {
                    variables: Vec::new(),
                },
            ],
        }
    }

    fn num_variables(&self) -> usize {
        self.variables.len() - 1
    }
}

impl HierarchicalPrefix {
    /// Creates a new scope with given quantification type
    pub fn new_scope(&mut self, quantifier: Quantifier) -> ScopeId {
        let last_scope: ScopeId = self.last_scope();
        if last_scope % 2 == quantifier as i32 {
            return last_scope;
        } else {
            self.scopes.push(Scope::new());
            return self.last_scope();
        }
    }

    /// Returns the last created scope
    pub fn last_scope(&self) -> ScopeId {
        assert!(self.scopes.len() > 0);
        (self.scopes.len() - 1) as ScopeId
    }

    /// Makes sure variable vector is large enough
    fn import(&mut self, variable: Variable) {
        if self.variables.len() <= variable as usize {
            self.variables.resize(
                (variable + 1) as usize,
                VariableInfo {
                    scope: -1,
                    is_universal: false,
                },
            )
        }
    }

    /// Adds a variable to a given scope
    ///
    /// Panics, if variable is already bound or scope does not exist (use new_scope first)
    pub fn add_variable(&mut self, variable: Variable, scope_id: ScopeId) {
        self.import(variable);
        if self.variables[variable as usize].is_bound() {
            panic!("variable cannot be bound twice");
        }
        if scope_id > self.last_scope() {
            panic!("scope does not exists");
        }
        let variable_info = &mut self.variables[variable as usize];
        variable_info.scope = scope_id;
        variable_info.is_universal = scope_id % 2 == 1;
        let scope = &mut self.scopes[scope_id as usize];
        scope.variables.push(variable);
    }
}
