use super::*;
use std::cmp::Ordering;

pub type ScopeId = usize;

#[derive(Debug, Clone)]
pub struct DQVariableInfo {
    bound: bool,
    scope_id: Option<ScopeId>,
    dependencies: FxHashSet<Variable>,
}

impl VariableInfo for DQVariableInfo {
    fn new() -> DQVariableInfo {
        DQVariableInfo {
            scope_id: None,
            bound: false,
            dependencies: FxHashSet::default(),
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
    pub dependencies: FxHashSet<Variable>,
    pub existentials: Vec<Variable>,
}

impl Scope {
    fn new(dependencies: &FxHashSet<Variable>) -> Scope {
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
    pub scopes: Vec<Scope>,
}

impl DependencyPrefix {
    pub fn add_existential(&mut self, variable: Variable, dependencies: &FxHashSet<Variable>) {
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

    fn get_scope(&self, dependencies: &FxHashSet<Variable>) -> Option<ScopeId> {
        for (scope_id, scope) in self.scopes.iter().enumerate() {
            if scope.dependencies == *dependencies {
                return Some(scope_id);
            }
        }
        None
    }

    /// makes sure that for every pair of scopes, the intersection of dependencies
    /// is contained as well
    pub fn build_closure(&mut self) {
        let mut to_add = Vec::new();
        let mut union = FxHashSet::default();
        loop {
            // TODO: there is probably a more efficient way, but the number of scopes is usually small anyways
            let mut changed = false;
            for (i, scope) in self.scopes.iter().enumerate() {
                for other in &self.scopes[i + 1..] {
                    let intersection: FxHashSet<Variable> = scope
                        .dependencies
                        .intersection(&other.dependencies)
                        .map(|x| *x)
                        .collect();
                    if self.get_scope(&intersection).is_none() {
                        // intersection is not contained
                        to_add.push(intersection);
                        changed = true;
                    }
                }
                union = union.union(&scope.dependencies).map(|x| *x).collect();
            }
            for dependencies in &to_add {
                if self.get_scope(dependencies).is_none() {
                    // intersection is not contained
                    self.scopes.push(Scope::new(dependencies));
                }
            }
            to_add.clear();
            if !changed {
                break;
            }
        }
        if self.get_scope(&union).is_none() {
            // union of all universal variables not contained
            self.scopes.push(Scope::new(&union));
        }
    }

    /// Builds the antichain decomposition of the dependency lattice
    pub fn antichain_decomposition(&self) -> Vec<Vec<ScopeId>> {
        // sort scopes by superset inclusion
        let mut scopes: Vec<ScopeId> = (0..self.scopes.len()).collect();
        scopes.sort_unstable_by(|&scope, &other| {
            let lhs = &self.scopes[scope].dependencies;
            let rhs = &self.scopes[other].dependencies;
            if lhs.is_superset(rhs) {
                Ordering::Less
            } else if lhs.is_subset(rhs) {
                Ordering::Greater
            } else {
                Ordering::Equal
            }
        });

        // extract antichains
        let mut antichains = Vec::new();
        while let Some(characteristic) = scopes.pop() {
            let mut antichain = vec![characteristic];
            for &other in scopes.iter().rev() {
                let lhs = &self.scopes[characteristic].dependencies;
                let rhs = &self.scopes[other].dependencies;
                let incomparable = antichain.iter().fold(true, |val, ele| {
                    val && !lhs.is_subset(rhs) && !lhs.is_superset(rhs)
                });
                if incomparable {
                    antichain.push(other);
                }
            }
            scopes = scopes
                .iter()
                .filter(|ele| !antichain.contains(ele))
                .map(|x| *x)
                .collect();
            antichains.push(antichain);
        }
        antichains
    }

    /// Checks if an existential variable `var` depends on `other`.
    /// If `other` is existential, the dependencies of `other`
    /// have to be a subset of the dependencies of `var`.
    /// If `other` is universal, it has to be contained in the
    /// dependencies of `var`.
    pub fn depends_on(&self, var: Variable, other: Variable) -> bool {
        let info = self.variables().get(var);
        let scope_id = info.scope_id
            .expect("depends_on called on universal variable");
        let scope = &self.scopes[scope_id];
        let other_info = self.variables().get(other);
        if other_info.is_universal() {
            scope.dependencies.contains(&other)
        } else {
            let other_scope_id = other_info
                .scope_id
                .expect("other var should be existential");
            let other_scope = &self.scopes[other_scope_id];
            other_scope.dependencies.is_subset(&scope.dependencies)
        }
    }

    /// Checks if existential variables in `scope` may depend on `var`.
    /// If `var` is existential, the dependencies of `var`
    /// have to be a subset of the dependencies of `scope`.
    /// If `var` is universal, it has to be contained in the
    /// dependencies of `scope`.
    pub fn depends_on_scope(&self, scope: &Scope, var: Variable) -> bool {
        let info = self.variables().get(var);
        if info.is_universal() {
            scope.dependencies.contains(&var)
        } else {
            let scope_id = info.scope_id.expect("var should be existential");
            let other_scope = &self.scopes[scope_id];
            other_scope.dependencies.is_subset(&scope.dependencies)
        }
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
            self.add_existential(variable, &FxHashSet::default());
        }
    }

    fn reduce_universal(&self, clause: &mut Clause) {
        let dependencies = clause.iter().fold(FxHashSet::default(), |mut acc, v| {
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

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_closure() {
        let mut prefix = DependencyPrefix::new(4);
        prefix.add_universal(1);
        prefix.add_universal(2);
        let mut dep = FxHashSet::default();
        dep.insert(1);
        prefix.add_existential(3, &dep);
        dep.clear();
        dep.insert(2);
        prefix.add_existential(4, &dep);
        dep.clear();

        // empty set and complete set not contained before...
        assert!(prefix.get_scope(&dep).is_none());
        dep.insert(1);
        dep.insert(2);
        assert!(prefix.get_scope(&dep).is_none());
        dep.clear();

        // ... but after building closure
        prefix.build_closure();
        assert_eq!(prefix.get_scope(&dep), Some(2));
        dep.insert(1);
        dep.insert(2);
        assert_eq!(prefix.get_scope(&dep), Some(3));

        // check antichain decomposition
        // there are 3 antichains:
        // * singletons for empty set and complete set
        // * the set containing both incomparable sets
        let antichains = prefix.antichain_decomposition();
        assert_eq!(antichains.len(), 3);
        assert_eq!(antichains[0], vec![2]);
        assert_eq!(antichains[2], vec![3]);
        assert!(antichains[1].contains(&0) && antichains[1].contains(&1));
    }

    #[test]
    fn test_closure_recursive() {
        let mut prefix = DependencyPrefix::new(6);
        prefix.add_universal(1);
        prefix.add_universal(2);
        prefix.add_universal(3);
        let mut dep = FxHashSet::default();
        dep.insert(1);
        dep.insert(2);
        prefix.add_existential(4, &dep);
        dep.clear();
        dep.insert(2);
        dep.insert(3);
        prefix.add_existential(5, &dep);
        dep.clear();
        dep.insert(1);
        dep.insert(3);
        prefix.add_existential(6, &dep);
        dep.clear();

        // empty set not contained before...
        assert!(prefix.get_scope(&dep).is_none());

        // ... but after building closure
        prefix.build_closure();
        assert!(prefix.get_scope(&dep).is_some());

        let antichains = prefix.antichain_decomposition();
        assert_eq!(antichains.len(), 4);
    }

    #[test]
    fn test_dep_on() {
        let mut prefix = DependencyPrefix::new(6);
        prefix.add_universal(1);
        prefix.add_universal(2);
        let mut dep = FxHashSet::default();
        prefix.add_existential(3, &dep); // d 3 0
        dep.insert(1);
        prefix.add_existential(4, &dep); // d 4 1 0
        dep.clear();
        dep.insert(2);
        prefix.add_existential(5, &dep); // d 5 2 0
        dep.insert(1);
        prefix.add_existential(6, &dep); // d 6 1 2 0

        // 3
        assert!(!prefix.depends_on(3, 1));
        assert!(!prefix.depends_on(3, 2));
        assert!(prefix.depends_on(3, 3));
        assert!(!prefix.depends_on(3, 4));
        assert!(!prefix.depends_on(3, 5));
        assert!(!prefix.depends_on(3, 6));

        // 4
        assert!(prefix.depends_on(4, 1));
        assert!(!prefix.depends_on(4, 2));
        assert!(prefix.depends_on(4, 3));
        assert!(prefix.depends_on(4, 4));
        assert!(!prefix.depends_on(4, 5));
        assert!(!prefix.depends_on(4, 6));

        // 5
        assert!(!prefix.depends_on(5, 1));
        assert!(prefix.depends_on(5, 2));
        assert!(prefix.depends_on(5, 3));
        assert!(!prefix.depends_on(5, 4));
        assert!(prefix.depends_on(5, 5));
        assert!(!prefix.depends_on(5, 6));

        // 6
        assert!(prefix.depends_on(6, 1));
        assert!(prefix.depends_on(6, 2));
        assert!(prefix.depends_on(6, 3));
        assert!(prefix.depends_on(6, 4));
        assert!(prefix.depends_on(6, 5));
        assert!(prefix.depends_on(6, 6));
    }
}
