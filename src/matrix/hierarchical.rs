use super::*;
use ena::unify::{InPlaceUnificationTable, UnifyKey};
use log::{debug, info};
use rustc_hash::{FxHashMap, FxHashSet};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Copy, Clone)]
pub struct ScopeId(u32);

#[derive(Debug, Clone)]
pub struct QVariableInfo {
    pub(crate) scope_id: Option<ScopeId>,
    is_universal: bool,
    pub(crate) copy_of: Variable,
    dependencies: FxHashSet<Variable>,
    pub(crate) level: u32,
}

#[derive(Debug, Clone)]
pub struct Scope {
    pub(crate) id: ScopeId,
    pub(crate) level: u32,
    pub(crate) quant: Quantifier,
    pub(crate) variables: Vec<Variable>,
}

#[derive(Debug)]
pub struct HierarchicalPrefix {
    /// storage of variables
    variables: VariableStore<QVariableInfo>,
    /// indexed by `ScopeId`, actual storage of nodes
    pub(crate) scopes: Vec<Scope>,
    /// indexed by `ScopeId`, returns list of next nodes in tree
    pub(crate) next_scopes: Vec<Vec<ScopeId>>,
    /// the root scopes,
    pub(crate) roots: Vec<ScopeId>,
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum Quantifier {
    Existential,
    Universal,
}

impl std::fmt::Display for ScopeId {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl ScopeId {
    fn new(id: usize) -> ScopeId {
        ScopeId(id as u32)
    }

    pub(crate) fn to_usize(self) -> usize {
        self.0 as usize
    }

    pub(crate) const OUTERMOST: ScopeId = ScopeId(0);
}

impl VariableInfo for QVariableInfo {
    fn new() -> QVariableInfo {
        QVariableInfo {
            scope_id: None,
            is_universal: false,
            copy_of: 0u32.into(),
            dependencies: FxHashSet::default(),
            level: 0,
        }
    }

    fn is_universal(&self) -> bool {
        self.is_universal
    }

    fn is_bound(&self) -> bool {
        self.scope_id.is_some()
    }
}

impl Scope {
    fn new(id: ScopeId, level: u32, quant: Quantifier) -> Scope {
        Scope {
            id,
            level,
            quant,
            variables: Vec::new(),
        }
    }

    pub fn contains(&self, variable: Variable) -> bool {
        self.variables.iter().any(|var| *var == variable)
    }
}

impl Dimacs for Scope {
    fn dimacs(&self) -> String {
        let mut dimacs = String::new();
        dimacs.push_str(&self.quant.dimacs());
        dimacs.push(' ');
        for &variable in self.variables.iter() {
            dimacs.push_str(&format!("{} ", variable));
        }
        dimacs.push_str("0");
        dimacs
    }
}

impl Quantifier {
    pub fn swap(&self) -> Quantifier {
        match self {
            &Quantifier::Existential => Quantifier::Universal,
            &Quantifier::Universal => Quantifier::Existential,
        }
    }
}

impl Dimacs for Quantifier {
    fn dimacs(&self) -> String {
        match self {
            Quantifier::Existential => String::from("e"),
            Quantifier::Universal => String::from("a"),
        }
    }
}

impl Prefix for HierarchicalPrefix {
    type V = QVariableInfo;

    fn new(num_variables: usize) -> Self {
        HierarchicalPrefix {
            variables: VariableStore::new(num_variables),
            scopes: vec![Scope::new(ScopeId::OUTERMOST, 0, Quantifier::Existential)],
            next_scopes: vec![vec![]],
            roots: vec![ScopeId::OUTERMOST],
        }
    }

    fn variables(&self) -> &VariableStore<Self::V> {
        &self.variables
    }

    fn import(&mut self, variable: Variable) {
        if !self.variables().get(variable).is_bound() {
            // bound free variables at top level existential quantifier
            self.add_variable(variable, ScopeId::OUTERMOST);
        }
    }

    fn reduce_universal(&self, clause: &mut Clause) {
        clause.reduce_universal_qbf(self);
    }

    fn depends_on<V: Into<Variable>, U: Into<Variable>>(&self, var: V, other: U) -> bool {
        let var = var.into();
        let other = other.into();
        let info = self.variables().get(var);
        debug_assert!(info.is_existential());
        let other = self.variables().get(other);
        other.level < info.level
    }
}

impl HierarchicalPrefix {
    /// Creates a new scope with given quantification type
    pub(crate) fn new_scope(&mut self, prev: ScopeId, quantifier: Quantifier) -> ScopeId {
        let prev_scope = &self.scopes[prev.to_usize()];
        if prev_scope.quant == quantifier {
            prev
        } else {
            let id = self.create_scope(quantifier, prev_scope.level + 1);
            self.next_scopes[prev.to_usize()].push(id);
            id
        }
    }

    /// Only crates scope, does not link to previous scope
    fn create_scope(&mut self, quantifier: Quantifier, level: u32) -> ScopeId {
        let next_id = ScopeId::new(self.scopes.len());
        self.scopes.push(Scope::new(next_id, level, quantifier));
        self.next_scopes.push(Vec::new());
        debug_assert!(self.scopes.len() == self.next_scopes.len());
        next_id
    }
    /*
    /// Returns the last created scope
    pub fn last_scope(&self) -> ScopeId {
        debug_assert!(self.scopes.len() > 0);
        (self.scopes.len() - 1) as ScopeId
    }
    */

    /// Adds a variable to a given scope
    ///
    /// Panics, if variable is already bound or scope does not exist (use new_scope first)
    pub fn add_variable<V: Into<Variable>>(&mut self, variable: V, scope_id: ScopeId) {
        let variable = variable.into();
        self.variables.import(variable);
        if self.variables.get(variable).is_bound() {
            panic!("variable cannot be bound twice");
        }
        let variable_info = self.variables.get_mut(variable);
        let scope = &mut self.scopes[scope_id.to_usize()];
        variable_info.scope_id = Some(scope_id);
        variable_info.is_universal = scope.quant == Quantifier::Universal;
        variable_info.level = scope.level;
        scope.variables.push(variable);
    }
}

impl Dimacs for HierarchicalPrefix {
    fn dimacs(&self) -> String {
        let mut dimacs = String::new();
        // traverse prefix tree level by level
        let mut level = 0;
        while self.print_level(&mut dimacs, level) {
            level += 1;
        }
        dimacs
    }
}

impl HierarchicalPrefix {
    fn print_level(&self, dimacs: &mut String, level: u32) -> bool {
        self.roots
            .iter()
            .any(|&scope_id| self.print_level_recursive(dimacs, scope_id, level))
    }

    fn print_level_recursive(&self, dimacs: &mut String, scope_id: ScopeId, level: u32) -> bool {
        let scope = &self.scopes[scope_id.to_usize()];
        if scope.level == level {
            if !(scope.id == ScopeId::OUTERMOST && scope.variables.is_empty()) {
                dimacs.push_str(&format!("{}\n", scope.dimacs()));
            }
            true
        } else {
            debug_assert!(scope.level < level);
            self.next_scopes[scope_id.to_usize()]
                .iter()
                .any(|&child_id| self.print_level_recursive(dimacs, child_id, level))
        }
    }
}

impl UnifyKey for Variable {
    type Value = ();
    fn index(&self) -> u32 {
        self.into()
    }
    fn from_index(u: u32) -> Self {
        u.into()
    }
    fn tag() -> &'static str {
        "Variable"
    }
}

impl Matrix<HierarchicalPrefix> {
    pub fn unprenex_by_miniscoping(&mut self, collapse_empty_scopes: bool) {
        // we store for each variable the variable it is connected to (by some clause)
        let mut table: InPlaceUnificationTable<Variable> = InPlaceUnificationTable::new();
        table.reserve(self.prefix.variables().num_variables() + 1);
        for i in 0..self.prefix.variables().num_variables() + 1 {
            table.new_key(());
        }

        debug_assert!(self.prefix.roots.len() == 1);

        self.prefix.roots = self.unprenex_recursive(
            &mut table,
            *self.prefix.roots.first().unwrap(),
            collapse_empty_scopes,
        );
    }

    fn unprenex_recursive(
        &mut self,
        table: &mut InPlaceUnificationTable<Variable>,
        scope_id: ScopeId,
        collapse_empty_scopes: bool,
    ) -> Vec<ScopeId> {
        // recursion
        let next_scope_ids = &self.prefix.next_scopes[scope_id.to_usize()];
        debug_assert!(next_scope_ids.len() <= 1);
        if let Some(&next_id) = next_scope_ids.first() {
            let splitted = self.unprenex_recursive(table, next_id, collapse_empty_scopes);
            if splitted.len() == 1 {
                debug_assert_eq!(splitted, vec![next_id]);
                return vec![scope_id];
            }
            self.prefix.next_scopes[scope_id.to_usize()] = splitted;
        }

        let scope: &Scope = &self.prefix.scopes[scope_id.to_usize()];
        match scope.quant {
            Quantifier::Existential => {
                self.union_over_connecting_sets(scope_id, table);
                self.partition_scopes(scope_id, table, collapse_empty_scopes)
            }
            Quantifier::Universal => self.split_universal(scope_id, table),
        }
    }

    /// Unifies variables that appear together in clauses
    fn union_over_connecting_sets(
        &mut self,
        scope_id: ScopeId,
        table: &mut InPlaceUnificationTable<Variable>,
    ) {
        let scope: &Scope = &self.prefix.scopes[scope_id.to_usize()];
        for clause in self.clauses.iter() {
            let mut connection = None;
            for &literal in clause.iter() {
                let variable = literal.variable();
                let info = self.prefix.variables.get(variable);
                if !info.is_bound() || info.is_universal() || info.level < scope.level {
                    continue;
                }

                match connection {
                    None => {
                        connection = Some(variable);
                    }
                    Some(connecting_var) => {
                        table
                            .unify_var_var(connecting_var, variable)
                            .expect("unification cannot fail");
                    }
                }
            }
        }
    }

    /// Splits the current existential scope according to unification table, returns the new scopes
    fn partition_scopes(
        &mut self,
        scope_id: ScopeId,
        table: &mut InPlaceUnificationTable<Variable>,
        collapse_empty_scopes: bool,
    ) -> Vec<ScopeId> {
        let mut scope = self.prefix.scopes[scope_id.to_usize()].clone();
        let mut scopes: Vec<ScopeId> = Vec::new();

        let mut remaining_next = self.prefix.next_scopes[scope_id.to_usize()].clone();

        if scope.id == ScopeId::OUTERMOST && scope.variables.is_empty() {
            return remaining_next
                .into_iter()
                .enumerate()
                .map(|(i, next_scope_id)| {
                    let id = if i == 0 {
                        ScopeId::OUTERMOST
                    } else {
                        self.prefix.create_scope(Quantifier::Existential, 0)
                    };
                    self.prefix.next_scopes[id.to_usize()] = vec![next_scope_id];
                    id
                })
                .collect();
        }

        let first = *scope.variables.first().expect("scopes should not be empty");
        let level = scope.level;
        scope.variables.retain(|&var| {
            if table.unioned(var, first) {
                // variable is in the same equivalence class
                return true;
            }
            // check if variable belongs to already created scope
            for &other_id in scopes.iter() {
                let other = &mut self.prefix.scopes[other_id.to_usize()];
                debug_assert!(!other.variables.is_empty());
                if table.unioned(
                    var,
                    *other.variables.first().expect("scopes should not be empty"),
                ) {
                    other.variables.push(var);
                    return false;
                }
            }
            // need to create new scope
            let id = self.prefix.create_scope(Quantifier::Existential, level);
            self.prefix.scopes[id.to_usize()].variables.push(var);
            scopes.push(id);
            remaining_next.retain(|next_scope_id| {
                let next_universal_scope = &self.prefix.scopes[next_scope_id.to_usize()];
                // TODO: check for empty universal scopes
                assert!(!collapse_empty_scopes);
                let next_scope_id = *self.prefix.next_scopes[next_universal_scope.id.to_usize()]
                    .first()
                    .expect("universal scopes have exactly one child");
                let next_scope = &self.prefix.scopes[next_scope_id.to_usize()];

                let nvar = next_scope
                    .variables
                    .first()
                    .expect("scopes should not be empty");
                if table.unioned(var, *nvar) {
                    self.prefix.next_scopes[id.to_usize()].push(next_scope_id);
                    false
                } else {
                    true
                }
            });
            false
        });
        self.prefix.scopes[scope_id.to_usize()] = scope;
        self.prefix.next_scopes[scope_id.to_usize()] = remaining_next;

        scopes.insert(0, scope_id); // push original scope back in front

        info!("detected {} partitions at level {}", scopes.len(), level);
        scopes
    }

    /// Makes a copy of `scope` for every element in `next`.
    /// Renames universal variables if needed
    fn split_universal(
        &mut self,
        scope_id: ScopeId,
        table: &mut InPlaceUnificationTable<Variable>,
    ) -> Vec<ScopeId> {
        let next_scope_len = {
            let next_scopes = &self.prefix.next_scopes[scope_id.to_usize()];
            debug_assert!(!next_scopes.is_empty());

            if next_scopes.len() == 1 {
                // do not need to copy and rename
                return vec![scope_id];
            }
            debug_assert!(next_scopes.len() > 1);
            next_scopes.len()
        };

        let mut scope = self.prefix.scopes[scope_id.to_usize()].clone();

        scope.variables.sort();

        // more than one successor, have to rename variables

        let mut scopes = Vec::new();
        for i in 0..self.prefix.next_scopes[scope_id.to_usize()].len() {
            let new_scope_id = self.prefix.create_scope(Quantifier::Universal, scope.level);
            let mut new_vars = Vec::new();

            let next_scope = &self.prefix.next_scopes[scope_id.to_usize()][i];
            let scope_var = *self.prefix.scopes[next_scope.to_usize()]
                .variables
                .first()
                .expect("scope cannot be empty");

            // mapping from old variables to new copy
            // is modified lazyly below
            let mut renaming = FxHashMap::default();

            // update clauses and occurrence list
            let variables = &mut self.prefix.variables;
            for (i, ref mut clause) in self.clauses.iter_mut().enumerate() {
                let clause_id = i as ClauseId;
                // check if clause contains variables of inner group
                let needs_renaming = clause.iter().any(|&literal| {
                    let info = variables.get(literal.variable());
                    if info.is_universal() || info.level < scope.level {
                        return false;
                    }
                    table.unioned(literal.variable(), scope_var)
                });
                if !needs_renaming {
                    continue;
                }

                for literal in clause.iter_mut() {
                    if scope.variables.binary_search(&literal.variable()).is_err() {
                        // not a variable of current scope
                        continue;
                    }
                    let var = literal.variable();
                    let new_var = *renaming.entry(var).or_insert_with(|| {
                        variables.variables.push(QVariableInfo {
                            scope_id: Some(new_scope_id),
                            is_universal: true,
                            copy_of: var,
                            level: scope.level,
                            dependencies: FxHashSet::default(),
                        });
                        let new_var: Variable = variables.num_variables().into();
                        new_vars.push(new_var);
                        new_var
                    });

                    {
                        let entry = self
                            .occurrences
                            .entry(*literal)
                            .or_insert_with(|| panic!("inconsistent state"));
                        // remove old occurrence
                        entry
                            .iter()
                            .position(|&other_clause_id| other_clause_id == clause_id)
                            .map(|index| entry.remove(index));
                    }
                    *literal = Literal::new(new_var, literal.signed());
                    let entry = self.occurrences.entry(*literal).or_insert_with(Vec::new);
                    entry.push(clause_id);
                }
            }
            // it can happen that we build universal scopes without variables
            // this gets cleaned-up in the outer existential quantifier

            self.prefix.scopes[new_scope_id.to_usize()].variables = new_vars;
            self.prefix.next_scopes[new_scope_id.to_usize()] = vec![*next_scope];
            debug_assert_eq!(self.prefix.next_scopes[new_scope_id.to_usize()].len(), 1);

            scopes.push(new_scope_id);
        }
        debug_assert_eq!(next_scope_len, scopes.len());
        scopes
    }
}
