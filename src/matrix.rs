use super::*;

use std::collections::HashMap;

pub type ClauseId = u32;

pub trait Prefix {
    fn new(num_variables: usize) -> Self;

    fn num_variables(&self) -> usize;

    fn orig_num_variables(&self) -> usize;

    fn get(&self, variable: Variable) -> &VariableInfo;
}

#[derive(Debug)]
pub struct Matrix<P: Prefix> {
    pub prefix: P,
    pub clauses: Vec<Clause>,
    occurrences: HashMap<Literal, Vec<ClauseId>>,
    conflict: bool,
    pub orig_clause_num: usize,
}

impl<P: Prefix> Matrix<P> {
    pub fn new(num_variables: usize, num_clauses: usize) -> Matrix<P> {
        Matrix {
            prefix: P::new(num_variables),
            clauses: Vec::with_capacity(num_clauses),
            occurrences: HashMap::new(),
            conflict: false,
            orig_clause_num: num_clauses,
        }
    }

    pub fn add(&mut self, clause: Clause) {
        for &literal in clause.iter() {
            let occurrences = self.occurrences.entry(literal).or_insert(Vec::new());
            occurrences.push(self.clauses.len() as ClauseId);
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
    pub scope: ScopeId,
    pub is_universal: bool,
    pub copy_of: Variable,
}

impl VariableInfo {
    pub fn is_bound(&self) -> bool {
        self.scope >= 0
    }

    pub fn is_universal(&self) -> bool {
        debug_assert!(self.is_bound());
        self.scope % 2 == 1
    }

    pub fn is_existential(&self) -> bool {
        return !self.is_universal();
    }
}

#[derive(Debug)]
pub struct Scope {
    pub id: ScopeId,
    pub variables: Vec<Variable>,
}

impl Scope {
    fn new(id: ScopeId) -> Scope {
        Scope {
            id: id,
            variables: Vec::new(),
        }
    }

    pub fn contains(&self, variable: Variable) -> bool {
        self.variables
            .iter()
            .fold(false, |val, &var| val || var == variable)
    }
}

#[derive(Debug)]
pub struct HierarchicalPrefix {
    variables: Vec<VariableInfo>,
    pub scopes: Vec<Scope>,
    orig_var_num: usize,
}

#[derive(Eq, PartialEq)]
pub enum Quantifier {
    Existential,
    Universal,
}

impl Quantifier {
    pub fn swap(&self) -> Quantifier {
        match self {
            &Quantifier::Existential => Quantifier::Universal,
            &Quantifier::Universal => Quantifier::Existential,
        }
    }
}

impl From<usize> for Quantifier {
    fn from(item: usize) -> Self {
        if item % 2 == 0 {
            Quantifier::Existential
        } else {
            Quantifier::Universal
        }
    }
}

impl From<ScopeId> for Quantifier {
    fn from(item: ScopeId) -> Self {
        if item < 0 {
            panic!("scope id's have to be positive");
        }
        if item % 2 == 0 {
            Quantifier::Existential
        } else {
            Quantifier::Universal
        }
    }
}

impl Prefix for HierarchicalPrefix {
    fn new(num_variables: usize) -> Self {
        let mut variables = Vec::with_capacity(num_variables + 1);
        variables.push(VariableInfo {
            scope: -1,
            is_universal: false,
            copy_of: 0,
        });
        HierarchicalPrefix {
            variables: variables,
            scopes: vec![
                Scope {
                    id: 0,
                    variables: Vec::new(),
                },
            ],
            orig_var_num: num_variables,
        }
    }

    fn num_variables(&self) -> usize {
        self.variables.len() - 1
    }

    fn orig_num_variables(&self) -> usize {
        self.orig_var_num
    }

    fn get(&self, variable: Variable) -> &VariableInfo {
        let index = variable as usize;
        if index >= self.variables.len() {
            // variable was not bound prior
            return &VariableInfo {
                scope: -1,
                is_universal: false,
                copy_of: 0,
            };
        }
        &self.variables[index]
    }
}

impl HierarchicalPrefix {
    /// Creates a new scope with given quantification type
    pub fn new_scope(&mut self, quantifier: Quantifier) -> ScopeId {
        let last_scope: ScopeId = self.last_scope();
        if last_scope % 2 == quantifier as ScopeId {
            return last_scope;
        } else {
            self.scopes.push(Scope::new(last_scope + 1));
            return self.last_scope();
        }
    }

    /// Returns the last created scope
    pub fn last_scope(&self) -> ScopeId {
        debug_assert!(self.scopes.len() > 0);
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
                    copy_of: 0,
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

#[derive(Debug)]
pub struct TreePrefix {
    variables: Vec<VariableInfo>,
    pub roots: Vec<Box<ScopeNode>>,
    orig_var_num: usize,
}

#[derive(Debug)]
pub struct ScopeNode {
    pub scope: Scope,
    group: Variable,
    pub next: Vec<Box<ScopeNode>>,
}

impl Prefix for TreePrefix {
    fn new(num_variables: usize) -> Self {
        let mut variables = Vec::with_capacity(num_variables + 1);
        variables.push(VariableInfo {
            scope: -1,
            is_universal: false,
            copy_of: 0,
        });
        TreePrefix {
            variables: variables,
            roots: Vec::new(),
            orig_var_num: num_variables,
        }
    }

    fn num_variables(&self) -> usize {
        self.variables.len() - 1
    }

    fn orig_num_variables(&self) -> usize {
        self.orig_var_num
    }

    fn get(&self, variable: Variable) -> &VariableInfo {
        let index = variable as usize;
        if index >= self.variables.len() {
            // variable was not bound prior
            return &VariableInfo {
                scope: -1,
                is_universal: false,
                copy_of: 0,
            };
        }
        &self.variables[index]
    }
}

impl Matrix<HierarchicalPrefix> {
    pub fn unprenex_by_miniscoping(matrix: Self) -> Matrix<TreePrefix> {
        let prefix = matrix.prefix;
        let mut variables = prefix.variables;
        let mut scopes = prefix.scopes;
        let mut clauses = matrix.clauses;
        let mut occurrences = matrix.occurrences;

        // we store for each variable the variable it is connected to
        // we compact this by using the smallest variable as characteristic element
        let mut partitions = Vec::with_capacity(variables.len());
        for i in 0..variables.len() {
            partitions.push(i as Variable);
        }

        let mut prev_scopes = Vec::new();
        let mut quantifier = Quantifier::Existential;
        while let Some(scope) = scopes.pop() {
            match quantifier {
                Quantifier::Existential => {
                    Self::union_over_connecting_sets(&clauses, &scope, &mut partitions, &variables);
                    prev_scopes =
                        Self::partition_scopes(scope, &mut partitions, &mut variables, prev_scopes);
                }
                Quantifier::Universal => {
                    prev_scopes = Self::split_universal(
                        scope,
                        &partitions,
                        prev_scopes,
                        &mut variables,
                        &mut clauses,
                        &mut occurrences,
                    );
                }
            }

            quantifier = quantifier.swap();
        }

        let tree_prefix = TreePrefix {
            variables,
            roots: prev_scopes,
            orig_var_num: prefix.orig_var_num,
        };
        Matrix {
            prefix: tree_prefix,
            clauses: clauses,
            occurrences: occurrences,
            conflict: matrix.conflict,
            orig_clause_num: matrix.orig_clause_num,
        }
    }

    fn union_over_connecting_sets(
        clauses: &Vec<Clause>,
        scope: &Scope,
        partitions: &mut Vec<Variable>,
        variables: &Vec<VariableInfo>,
    ) {
        for clause in clauses.iter() {
            let mut connection = None;
            for &literal in clause.iter() {
                let variable = literal.variable() as usize;
                let info = &variables[variable as usize];
                if !info.is_bound() {
                    continue;
                }
                if info.is_universal() {
                    continue;
                }
                if info.scope < scope.id {
                    continue;
                }

                // Check whether this variable connects some variable sets
                loop {
                    // Compacitify
                    let characteristic_elem = partitions[variable] as usize;
                    if partitions[characteristic_elem] != partitions[variable] {
                        partitions[variable] = partitions[characteristic_elem];
                    } else {
                        break;
                    }
                }

                match connection {
                    None => {
                        connection = Some(partitions[variable]);
                        continue;
                    }
                    Some(connecting_var) => {
                        if connecting_var < partitions[variable] {
                            // connection var is smaller, update variable and characteristic element
                            let characteristic_elem = partitions[variable] as usize;
                            partitions[characteristic_elem] = connecting_var;
                            partitions[variable] = connecting_var;
                        }
                        if connecting_var > partitions[variable] {
                            // connection var is greater, update connection var
                            partitions[connecting_var as usize] = partitions[variable];
                            connection = Some(partitions[variable]);
                        }
                    }
                }
            }
        }
        // last compactify
        for i in 1..partitions.len() {
            loop {
                let characteristic_elem = partitions[i] as usize;
                partitions[i] = partitions[characteristic_elem];
                let characteristic_elem = partitions[i] as usize;
                if partitions[i] < i as Variable || partitions[i] == partitions[characteristic_elem]
                {
                    break;
                }
            }
        }
    }

    fn partition_scopes(
        scope: Scope,
        partitions: &mut Vec<Variable>,
        variables: &mut Vec<VariableInfo>,
        next: Vec<Box<ScopeNode>>,
    ) -> Vec<Box<ScopeNode>> {
        let mut scopes = Vec::new();

        let mut remaining_next = next;

        // maps characteristic variables to index of scopes vector
        let mut groups = HashMap::new();

        for i in 1..partitions.len() {
            let variable = i as Variable;
            {
                // we later access variables mutably
                let info = &variables[i];
                if !info.is_bound() {
                    continue;
                }
                if info.is_universal() {
                    continue;
                }
                if info.scope < scope.id {
                    continue;
                }
            }

            let partition = partitions[i];
            debug!("variable {} is in partition {}", i, partition);

            if partition == variable {
                // variable is chracteristic element of a variable group
                let mut node = Box::new(ScopeNode {
                    scope: Scope::new(scope.id),
                    group: partition,
                    next: Vec::new(),
                });
                if scope.contains(variable) {
                    node.scope.variables.push(variable);
                }

                // split next-scopes
                let mut j = 0;
                while j != remaining_next.len() {
                    if partitions[remaining_next[j].group as usize] == partition {
                        // scope belongs to this branch of tree
                        let mut next = remaining_next.remove(j);
                        if next.scope.variables.len() == 0 {
                            // the universal scope is empty, thus we can merge existential scope afterwards into currents scope
                            assert!(next.next.len() == 1);
                            let existential = next.next.pop().unwrap();
                            for &variable in existential.scope.variables.iter() {
                                node.scope.variables.push(variable);
                                variables[variable as usize].scope = node.scope.id;
                            }
                            node.next.extend(existential.next);
                        } else {
                            node.next.push(next);
                        }
                    } else {
                        j += 1;
                    }
                }

                scopes.push(node);
                groups.insert(variable, scopes.len() - 1);

            // TODO: sort clauses
            } else {
                // variable belongs to variable group represented by `partition`
                debug_assert!(partition < variable);
                let new_scope = &mut scopes[groups[&partition]];
                if scope.contains(variable) {
                    new_scope.scope.variables.push(variable);
                }
            }
        }

        info!("detected {} partitions at level {}", scopes.len(), scope.id);

        scopes
    }

    /// Makes a copy of `scope` for every element in `next`.
    /// Renames universal variables if needed
    fn split_universal(
        mut scope: Scope,
        partitions: &Vec<Variable>,
        next: Vec<Box<ScopeNode>>,
        variables: &mut Vec<VariableInfo>,
        clauses: &mut Vec<Clause>,
        occurrences: &mut HashMap<Literal, Vec<ClauseId>>,
    ) -> Vec<Box<ScopeNode>> {
        debug_assert!(!next.is_empty());

        if next.len() == 1 {
            // do not need to copy and rename
            let mut node = Box::new(ScopeNode {
                scope: Scope::new(scope.id),
                group: next[0].group,
                next: next,
            });
            node.scope.variables.extend(scope.variables.clone());
            return vec![node];
        }

        scope.variables.sort();

        // more than one successor, have to rename variables
        debug_assert!(next.len() > 1);
        let mut scopes = Vec::new();
        for next_scope in next {
            let mut new_scope = Scope::new(scope.id);

            // mapping from old variables to new copy
            // is modified lazyly below
            let mut renaming = HashMap::new();

            // update clauses and occurrence list
            for (i, ref mut clause) in clauses.iter_mut().enumerate() {
                let clause_id = i as ClauseId;
                // check if clause contains variables of inner group
                let needs_renaming = clause.iter().fold(false, |val, &literal| {
                    let info = &variables[literal.variable() as usize];
                    if info.is_universal() {
                        return val;
                    }
                    if info.scope < scope.id {
                        return val;
                    }
                    if partitions[literal.variable() as usize] == next_scope.group {
                        return true;
                    } else {
                        return val;
                    }
                });
                if needs_renaming {
                    for ref mut literal in clause.iter_mut() {
                        if scope.variables.binary_search(&literal.variable()).is_err() {
                            // not a variable of current scope
                            continue;
                        }
                        let var = literal.variable();
                        if !renaming.contains_key(&var) {
                            variables.push(VariableInfo {
                                scope: scope.id,
                                is_universal: true,
                                copy_of: var,
                            });
                            let new_var = (variables.len() - 1) as Variable;
                            new_scope.variables.push(new_var);
                            renaming.insert(var, new_var);
                        }
                        let new_var = *renaming.get(&var).unwrap();

                        {
                            let entry = occurrences
                                .entry(**literal)
                                .or_insert_with(|| panic!("inconsistent state"));
                            // remove old occurrence
                            entry
                                .iter()
                                .position(|&other_clause_id| other_clause_id == clause_id)
                                .map(|index| entry.remove(index));
                        }
                        **literal = Literal::new(new_var, literal.signed());
                        let entry = occurrences.entry(**literal).or_insert(Vec::new());
                        entry.push(clause_id);
                    }
                }
            }
            // it can happen that we build universal scopes without variables
            // this gets cleaned-up in the outer existential quantifier

            let mut node = Box::new(ScopeNode {
                scope: new_scope,
                group: next_scope.group,
                next: vec![next_scope],
            });
            scopes.push(node);
        }
        scopes
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
        let matrix = qdimacs::parse(&instance).unwrap();
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
        let matrix = qdimacs::parse(&instance).unwrap();
        let matrix = Matrix::unprenex_by_miniscoping(matrix);
        assert!(matrix.prefix.roots.len() == 2);
    }
}
