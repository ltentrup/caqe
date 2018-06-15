use super::*;

use std::collections::HashSet;

pub type ScopeId = usize;

#[derive(Debug, Clone)]
pub struct DQVariableInfo {
    pub is_universal: bool,
    dependencies: HashSet<Variable>,
}

impl VariableInfo for DQVariableInfo {
    fn new() -> DQVariableInfo {
        DQVariableInfo {
            is_universal: false,
            dependencies: HashSet::new(),
        }
    }
}

/// A scope represents a grouping of existential variables with the same dependency set
#[derive(Debug)]
pub struct Scope {
    dependencies: HashSet<Variable>,
    existentials: HashSet<Variable>,
}

impl Scope {
    fn new() -> Scope {
        Scope {
            dependencies: HashSet::new(),
            existentials: HashSet::new(),
        }
    }

    fn new_empty(dependencies: HashSet<Variable>) -> Scope {
        Scope {
            dependencies,
            existentials: HashSet::new(),
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
