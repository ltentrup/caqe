use super::*;

use std::collections::HashSet;

pub type ScopeId = usize;

#[derive(Debug, Clone)]
pub struct DQVariableInfo {
    bound: bool,
    scope_id: Option<ScopeId>,
    dependencies: HashSet<Variable>,
}

impl VariableInfo for DQVariableInfo {
    fn new() -> DQVariableInfo {
        DQVariableInfo {
            scope_id: None,
            bound: false,
            dependencies: HashSet::new(),
        }
    }
}

impl DQVariableInfo {
    pub fn is_bound(&self) -> bool {
        self.bound
    }

    pub fn is_universal(&self) -> bool {
        debug_assert!(self.is_bound());
        self.scope_id.is_none()
    }

    pub fn is_existential(&self) -> bool {
        !self.is_universal()
    }
}

/// A scope represents a grouping of existential variables with the same dependency set
#[derive(Debug)]
pub struct Scope {
    dependencies: HashSet<Variable>,
    existentials: Vec<Variable>,
}

impl Scope {
    fn new(dependencies: &HashSet<Variable>) -> Scope {
        Scope {
            dependencies: dependencies.clone(),
            existentials: Vec::new(),
        }
    }

    pub fn contains(&self, variable: Variable) -> bool {
        self.existentials.contains(&variable)
    }
}

impl Dimacs for Scope {
    fn dimacs(&self) -> String {
        let mut dimacs = String::new();
        for &variable in self.existentials.iter() {
            dimacs.push_str(&format!("d {} ", variable));
            for &dependency in self.dependencies.iter() {
                dimacs.push_str(&format!("{} ", dependency));
            }
            dimacs.push_str("0");
        }
        dimacs
    }
}

#[derive(Debug)]
pub struct DependencyPrefix {
    variables: VariableStore<DQVariableInfo>,
    scopes: Vec<Scope>,
}

impl DependencyPrefix {
    pub fn add_existential(&mut self, variable: Variable, dependencies: &HashSet<Variable>) {
        self.variables.import(variable);
        if self.variables.get(variable).is_bound() {
            panic!("variable cannot be bound twice");
        }
        let scope_id = match self.get_scope(dependencies) {
            None => {
                let scope_id = self.scopes.len();
                self.scopes.push(Scope::new(dependencies));
                scope_id
            }
            Some(scope_id) => scope_id,
        };
        let scope = self.scopes
            .get_mut(scope_id)
            .expect("scope is guaranteed to exists");
        scope.existentials.push(variable);

        let variable_info = self.variables.get_mut(variable);
        variable_info.scope_id = Some(scope_id);
        variable_info.bound = true;
    }

    pub fn add_universal(&mut self, variable: Variable) {
        self.variables.import(variable);
        if self.variables.get(variable).is_bound() {
            panic!("variable cannot be bound twice");
        }
        let variable_info = self.variables.get_mut(variable);
        variable_info.scope_id = None;
        variable_info.bound = true;
    }

    fn get_scope(&self, dependencies: &HashSet<Variable>) -> Option<ScopeId> {
        for (scope_id, scope) in self.scopes.iter().enumerate() {
            if scope.dependencies == *dependencies {
                return Some(scope_id);
            }
        }
        None
    }
}

impl Prefix for DependencyPrefix {
    type V = DQVariableInfo;

    fn new(num_variables: usize) -> Self {
        DependencyPrefix {
            variables: VariableStore::new(num_variables),
            scopes: Vec::new(),
        }
    }
    fn variables(&self) -> &VariableStore<Self::V> {
        &self.variables
    }

    fn import(&mut self, variable: Variable) {
        if !self.variables().get(variable).is_bound() {
            // bound free variables at top level existential quantifier, i.e., without dependencies
            self.add_existential(variable, &HashSet::new());
        }
    }
    fn reduce_universal(&self, clause: &mut Clause) {
        let dependencies = clause.iter().fold(HashSet::new(), |mut acc, v| {
            match self.variables().get(v.variable()).scope_id {
                None => acc,
                Some(scope_id) => {
                    for var in &self.scopes[scope_id].dependencies {
                        acc.insert(var);
                    }
                    acc
                }
            }
        });
        clause.retain(|l| {
            if self.variables().get(l.variable()).is_universal() {
                dependencies.contains(&l.variable())
            } else {
                // retain all existential literals
                true
            }
        });
    }
}
