use super::*;
use dot;
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
    fn new(id: usize) -> Self {
        Self(id as u32)
    }

    pub(crate) fn to_usize(self) -> usize {
        self.0 as usize
    }

    pub(crate) const OUTERMOST: Self = Self(0);
}

impl VariableInfo for QVariableInfo {
    fn new() -> Self {
        Self {
            scope_id: None,
            is_universal: false,
            copy_of: 0_u32.into(),
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

    fn remove_dependency(&mut self, spurious: Variable) {
        self.dependencies.remove(&spurious);
    }

    fn dependencies(&self) -> &FxHashSet<Variable> {
        &self.dependencies
    }
}

impl Scope {
    fn new(id: ScopeId, level: u32, quant: Quantifier) -> Self {
        Self {
            id,
            level,
            quant,
            variables: Vec::new(),
        }
    }

    #[allow(dead_code)]
    pub fn contains(&self, variable: Variable) -> bool {
        self.variables.iter().any(|var| *var == variable)
    }
}

impl Dimacs for Scope {
    fn dimacs(&self) -> String {
        let mut dimacs = String::new();
        dimacs.push_str(&self.quant.dimacs());
        dimacs.push(' ');
        for &variable in &self.variables {
            dimacs.push_str(&format!("{} ", variable));
        }
        dimacs.push_str("0");
        dimacs
    }
}

impl Quantifier {
    #[allow(dead_code)]
    pub fn swap(self) -> Self {
        match self {
            Quantifier::Existential => Quantifier::Universal,
            Quantifier::Universal => Quantifier::Existential,
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
        Self {
            variables: VariableStore::new(num_variables),
            scopes: vec![Scope::new(ScopeId::OUTERMOST, 0, Quantifier::Existential)],
            next_scopes: vec![vec![]],
            roots: vec![ScopeId::OUTERMOST],
        }
    }

    fn variables(&self) -> &VariableStore<Self::V> {
        &self.variables
    }
    fn mut_vars(&mut self) -> &mut VariableStore<Self::V> {
        &mut self.variables
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
        let other_info = self.variables().get(other);
        if other_info.is_universal {
            info.dependencies.contains(&other)
        } else {
            let res = other_info.dependencies.is_subset(&info.dependencies);
            debug_assert!(!res || other_info.level < info.level);
            res
        }
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

    /// Compute the dependency of existential variables by prefix tree traversal
    pub(crate) fn compute_dependencies(&mut self) {
        fn compute_dependencies_recursive(
            scopes: &[Scope],
            next_scopes: &[Vec<ScopeId>],
            variables: &mut VariableStore<QVariableInfo>,
            prior_deps: &FxHashSet<Variable>,
            scope_id: ScopeId,
        ) {
            let scope = &scopes[scope_id.to_usize()];
            let new_deps = match scope.quant {
                Quantifier::Existential => {
                    for var in &scope.variables {
                        variables.get_mut(*var).dependencies = prior_deps.clone();
                    }
                    prior_deps.clone()
                }
                Quantifier::Universal => {
                    let mut new = prior_deps.clone();
                    new.extend(&scope.variables);
                    new
                }
            };
            for next_scope_id in &next_scopes[scope_id.to_usize()] {
                compute_dependencies_recursive(
                    scopes,
                    next_scopes,
                    variables,
                    &new_deps,
                    *next_scope_id,
                );
            }
        }

        let current_deps = FxHashSet::default();
        for scope_id in &self.roots {
            compute_dependencies_recursive(
                &self.scopes,
                &self.next_scopes,
                &mut self.variables,
                &current_deps,
                *scope_id,
            );
        }
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
    pub fn unprenex_by_miniscoping(&mut self) {
        // we store for each variable the variable it is connected to (by some clause)
        let mut table: InPlaceUnificationTable<Variable> = InPlaceUnificationTable::new();
        table.reserve(self.prefix.variables().max_variable_id() + 1);
        for _ in 0..=self.prefix.variables().max_variable_id() {
            table.new_key(());
        }

        debug_assert!(self.prefix.roots.len() == 1);

        self.prefix.roots =
            self.unprenex_recursive(&mut table, *self.prefix.roots.first().unwrap());

        self.prefix.compute_dependencies();

        //self.prefix.print_dot_repr();

        // post-processing: repair invariants
        self.prefix.fix_levels();
        //self.prefix.renumber_scopes();

        //self.prefix.print_dot_repr();

        #[cfg(feature = "debug_assertions")]
        self.prefix.check_invariants();
    }

    fn unprenex_recursive(
        &mut self,
        table: &mut InPlaceUnificationTable<Variable>,
        scope_id: ScopeId,
    ) -> Vec<ScopeId> {
        // recursion
        let next_scope_ids = &self.prefix.next_scopes[scope_id.to_usize()];
        debug_assert!(next_scope_ids.len() <= 1);
        if let Some(&next_id) = next_scope_ids.first() {
            let splitted = self.unprenex_recursive(table, next_id);
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
                self.partition_scopes(scope_id, table)
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
        for clause in &self.clauses {
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
    ) -> Vec<ScopeId> {
        let mut scope = self.prefix.scopes[scope_id.to_usize()].clone();
        let mut scopes: Vec<ScopeId> = Vec::new();
        let mut existentials: Vec<ScopeId> = Vec::new();

        let mut remaining_next = self.prefix.next_scopes[scope_id.to_usize()].clone();

        // filter existential next scopes
        remaining_next.retain(|&other_scope_id| {
            let scope = &self.prefix.scopes[other_scope_id.to_usize()];
            match scope.quant {
                Quantifier::Universal => true,
                Quantifier::Existential => {
                    existentials.push(other_scope_id);
                    false
                }
            }
        });

        if scope.id == ScopeId::OUTERMOST && scope.variables.is_empty() {
            assert!(scopes.is_empty());
            let mut res: Vec<ScopeId> = remaining_next
                .into_iter()
                .enumerate()
                .map(|(i, next_scope_id)| {
                    let id = if i == 0 {
                        ScopeId::OUTERMOST
                    } else {
                        self.prefix.create_scope(Quantifier::Existential, 0)
                    };
                    /*debug_assert_eq!(
                        self.prefix.scopes[next_scope_id.to_usize()].quant,
                        Quantifier::Existential
                    );*/
                    self.prefix.next_scopes[id.to_usize()] = vec![next_scope_id];
                    id
                })
                .collect();
            res.extend(existentials);
            return res;
        }

        scopes.push(scope_id); // push original scope back in front

        let first = *scope.variables.first().expect("scopes should not be empty");
        let level = scope.level;

        scope.variables.retain(|&var| {
            debug!("first {}, var {}", first, var);
            if table.unioned(var, first) {
                // variable is in the same equivalence class
                return true;
            }
            // check if variable belongs to already created scope
            for &other_id in &scopes {
                let other = &mut self.prefix.scopes[other_id.to_usize()];
                debug_assert!(!other.variables.is_empty());
                if table.unioned(
                    var,
                    *other.variables.first().expect("scopes should not be empty"),
                ) {
                    other.variables.push(var);
                    self.prefix.variables.get_mut(var).scope_id = Some(other_id);
                    return false;
                }
            }
            // need to create new scope
            let id = self.prefix.create_scope(Quantifier::Existential, level);
            self.prefix.scopes[id.to_usize()].variables.push(var);
            self.prefix.variables.get_mut(var).scope_id = Some(id);
            scopes.push(id);
            remaining_next.retain(|next_univ_scope_id| {
                debug!(
                    "check if {} is connected with var {}",
                    next_univ_scope_id, var,
                );
                let next_universal_scope = &self.prefix.scopes[next_univ_scope_id.to_usize()];
                debug_assert_eq!(next_universal_scope.quant, Quantifier::Universal);
                debug_assert!(!next_universal_scope.variables.is_empty());
                let next_exist_scope_id = *self.prefix.next_scopes
                    [next_universal_scope.id.to_usize()]
                .first()
                .expect("universal scopes have exactly one child");
                let next_scope = &self.prefix.scopes[next_exist_scope_id.to_usize()];

                let nvar = next_scope
                    .variables
                    .first()
                    .expect("scopes should not be empty");
                if table.unioned(var, *nvar) {
                    self.prefix.next_scopes[id.to_usize()].push(*next_univ_scope_id);
                    false
                } else {
                    true
                }
            });
            false
        });

        // check if they are connnected with some scope
        for existential_scope_id in existentials {
            let existential_scope = &self.prefix.scopes[existential_scope_id.to_usize()].clone();
            debug_assert_eq!(existential_scope.quant, Quantifier::Existential);
            debug_assert!(!existential_scope.variables.is_empty());
            let evar = existential_scope
                .variables
                .first()
                .expect("existential scopes should not be empty");
            let mut merged = false;
            for other_id in &scopes {
                debug!(
                    "check if {} is connected to {}",
                    existential_scope_id, other_id
                );
                let other_scope = &self.prefix.scopes[other_id.to_usize()];
                let level = other_scope.level;
                debug_assert_eq!(other_scope.quant, Quantifier::Existential);
                debug_assert!(!other_scope.variables.is_empty());
                let other_var = other_scope
                    .variables
                    .first()
                    .expect("existential scopes should not be empty");
                if table.unioned(*evar, *other_var) {
                    // merge scopes
                    merged = true;
                    debug!("merge scope {} into {}", existential_scope_id, other_id);
                    for move_var in &existential_scope.variables {
                        if *other_id == scope.id {
                            scope.variables.push(*move_var); // special cases since it is overwritten later
                        } else {
                            self.prefix.scopes[other_id.to_usize()]
                                .variables
                                .push(*move_var);
                        }
                        self.prefix.mut_vars().get_mut(*move_var).scope_id = Some(*other_id);
                        self.prefix.mut_vars().get_mut(*move_var).level = level;
                    }
                    self.prefix.scopes[existential_scope_id.to_usize()]
                        .variables
                        .clear();
                    let successors = std::mem::replace(
                        &mut self.prefix.next_scopes[existential_scope_id.to_usize()],
                        Vec::new(),
                    );
                    if *other_id == scope.id {
                        remaining_next.extend(successors); // special cases since it is overwritten later
                    } else {
                        self.prefix.next_scopes[other_id.to_usize()].extend(successors);
                    }

                    break;
                }
            }
            if !merged {
                scopes.push(existential_scope_id)
            }
        }

        // filter non-connected universal scopes
        remaining_next.retain(|&next_univ_scope_id| {
            let next_universal_scope = &self.prefix.scopes[next_univ_scope_id.to_usize()];
            debug_assert_eq!(next_universal_scope.quant, Quantifier::Universal);

            let next_exist_scope_id = *self.prefix.next_scopes[next_universal_scope.id.to_usize()]
                .first()
                .expect("universal scopes have exactly one child");
            let next_scope = &self.prefix.scopes[next_exist_scope_id.to_usize()];

            let nvar = next_scope
                .variables
                .first()
                .expect("scopes should not be empty");
            debug!(
                "check if {} is connected with {}",
                next_univ_scope_id, scope_id
            );
            if !table.unioned(first, *nvar) {
                scopes.push(next_univ_scope_id);
                false
            } else {
                true
            }
        });

        self.prefix.scopes[scope_id.to_usize()] = scope;
        self.prefix.next_scopes[scope_id.to_usize()] = remaining_next;

        info!("detected {} partitions at level {}", scopes.len(), level);
        //dbg!(&scopes);
        scopes
    }

    /// Makes a copy of `scope` for every element in `next`.
    /// Renames universal variables if needed
    fn split_universal(
        &mut self,
        scope_id: ScopeId,
        table: &mut InPlaceUnificationTable<Variable>,
    ) -> Vec<ScopeId> {
        let mut remaining_next = self.prefix.next_scopes[scope_id.to_usize()].clone();
        debug_assert!(!remaining_next.is_empty());

        if remaining_next.len() == 1 {
            // do not need to copy and rename
            debug_assert_eq!(
                self.prefix.scopes[remaining_next[0].to_usize()].quant,
                Quantifier::Universal
            );
            return vec![scope_id];
        }
        debug_assert!(remaining_next.len() > 1);

        let mut scope = self.prefix.scopes[scope_id.to_usize()].clone();
        scope.variables.sort(); // for binary search

        let mut scopes = Vec::new();

        // filter universal scopes and add them to this level
        remaining_next.retain(|&next_scope_id| {
            let next_scope = &self.prefix.scopes[next_scope_id.to_usize()];
            match next_scope.quant {
                Quantifier::Existential => true,
                Quantifier::Universal => {
                    scopes.push(next_scope_id);

                    let mut renaming = FxHashMap::default();

                    debug_assert_eq!(self.prefix.next_scopes[next_scope_id.to_usize()].len(), 1);
                    let exist_scope_id = self.prefix.next_scopes[next_scope_id.to_usize()]
                        .first()
                        .expect("has exactly one successor");
                    let scope_var = self.prefix.scopes[exist_scope_id.to_usize()]
                        .variables
                        .first()
                        .expect("existential scopes should not be empty");

                    let new_vars = self.rename_universals(
                        &scope,
                        table,
                        &mut renaming,
                        *scope_var,
                        next_scope_id,
                    );
                    self.prefix.scopes[next_scope_id.to_usize()]
                        .variables
                        .extend(new_vars);
                    false
                }
            }
        });

        // more than one successor, have to rename variables
        for &next_scope_id in remaining_next.iter().skip(1) {
            let new_scope_id = self.prefix.create_scope(Quantifier::Universal, scope.level);

            debug_assert_eq!(
                self.prefix.scopes[next_scope_id.to_usize()].quant,
                Quantifier::Existential
            );
            let scope_var = *self.prefix.scopes[next_scope_id.to_usize()]
                .variables
                .first()
                .expect("scope cannot be empty");

            // mapping from old variables to new copy
            // is modified lazily below
            let mut renaming = FxHashMap::default();

            let new_vars =
                self.rename_universals(&scope, table, &mut renaming, scope_var, new_scope_id);

            if new_vars.is_empty() {
                // universal scope is empty, push existential scope instead
                scopes.push(next_scope_id);
            } else {
                self.prefix.scopes[new_scope_id.to_usize()].variables = new_vars;
                self.prefix.next_scopes[new_scope_id.to_usize()] = vec![next_scope_id];
                debug_assert_eq!(self.prefix.next_scopes[new_scope_id.to_usize()].len(), 1);

                scopes.push(new_scope_id);
            }
        }
        // update original scope
        self.prefix.next_scopes[scope_id.to_usize()] = vec![remaining_next[0]];
        scopes.insert(0, scope_id);
        scopes
    }

    fn rename_universals(
        &mut self,
        scope: &Scope,
        table: &mut InPlaceUnificationTable<Variable>,
        renaming: &mut FxHashMap<Variable, Variable>,
        scope_var: Variable,
        new_scope_id: ScopeId,
    ) -> Vec<Variable> {
        let mut new_vars = Vec::new();

        // update clauses and occurrence list
        let variables = &mut self.prefix.variables;
        for (i, clause) in self.clauses.iter_mut().enumerate() {
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
                    let new_var: Variable = variables.max_variable_id().into();
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
        new_vars
    }
}

impl HierarchicalPrefix {
    fn fix_levels(&mut self) {
        fn fix_levels_recursive(
            scopes: &mut Vec<Scope>,
            next_scopes: &[Vec<ScopeId>],
            variables: &mut VariableStore<QVariableInfo>,
            level: u32,
            scope_id: ScopeId,
        ) {
            let scope = &mut scopes[scope_id.to_usize()];
            scope.level = level;

            for var in &scope.variables {
                variables.get_mut(*var).level = level;
            }

            for next_scope_id in &next_scopes[scope_id.to_usize()] {
                fix_levels_recursive(scopes, next_scopes, variables, level + 1, *next_scope_id);
            }
        }

        for scope_id in &self.roots {
            fix_levels_recursive(
                &mut self.scopes,
                &self.next_scopes,
                &mut self.variables,
                0,
                *scope_id,
            );
        }
    }

    /// Ensures that scopes are numbered in pre-order w.r.t. the quantifier prefix tree
    #[allow(dead_code)]
    fn renumber_scopes(&mut self) {
        fn renumber_scopes_recursive(
            variables: &mut VariableStore<QVariableInfo>,
            scopes: &[Scope],
            next_scopes: &[Vec<ScopeId>],
            new_scopes: &mut Vec<Scope>,
            new_next_scopes: &mut Vec<Vec<ScopeId>>,
            scope_id: ScopeId,
        ) -> ScopeId {
            let mut scope = scopes[scope_id.to_usize()].clone();
            let new_id = ScopeId::new(new_scopes.len());
            scope.id = new_id;
            for var in &scope.variables {
                variables.get_mut(*var).scope_id = Some(new_id);
            }
            new_scopes.push(scope);
            new_next_scopes.push(Vec::new());
            debug_assert_eq!(new_scopes.len(), new_next_scopes.len());

            for &next_scope_id in &next_scopes[scope_id.to_usize()] {
                let new_next_id = renumber_scopes_recursive(
                    variables,
                    scopes,
                    next_scopes,
                    new_scopes,
                    new_next_scopes,
                    next_scope_id,
                );
                new_next_scopes[new_id.to_usize()].push(new_next_id);
            }

            new_id
        }

        let mut new_scopes = Vec::new();
        let mut new_next_scopes = Vec::new();

        let roots = self.roots.clone();
        self.roots = roots
            .iter()
            .map(|&scope_id| {
                renumber_scopes_recursive(
                    &mut self.variables,
                    &self.scopes,
                    &self.next_scopes,
                    &mut new_scopes,
                    &mut new_next_scopes,
                    scope_id,
                )
            })
            .collect();
        self.scopes = new_scopes;
        self.next_scopes = new_next_scopes;
    }

    /// Checks that the prefix maintains the following invariants
    /// * a variable bound at some scope with id `n` has scope_id `n` in its variables info
    /// * the scope_id's are numbered in pre-order of the prefix tree
    ///
    /// panics if an invariant does not hold
    #[cfg(feature = "debug_assertions")]
    fn check_invariants(&self) {
        self.roots
            .iter()
            .for_each(|&root| self.check_invariants_recursive(root));
    }

    #[cfg(feature = "debug_assertions")]
    fn check_invariants_recursive(&self, scope_id: ScopeId) {
        let scope = &self.scopes[scope_id.to_usize()];
        for &var in &scope.variables {
            let info = self.variables().get(var);
            assert_eq!(
                scope.id,
                info.scope_id.expect("variable is bound"),
                "{:?}\n{:?}",
                scope,
                info
            );
        }
        /*let mut prev_scope_id = ScopeId(0);
        for &next_scope_id in &self.next_scopes[scope_id.to_usize()] {
            self.check_invariants_recursive(next_scope_id);

            // check that the scope-ids in the prefix tree are nubered correctly
            assert!(next_scope_id > scope_id);
            assert!(next_scope_id > prev_scope_id);
            prev_scope_id = next_scope_id;
        }*/
    }
}

type Nd = ScopeId;
type Ed = (Nd, Nd);

impl<'a> dot::Labeller<'a, Nd, Ed> for &HierarchicalPrefix {
    fn graph_id(&'a self) -> dot::Id<'a> {
        dot::Id::new("quantifier_prefix").unwrap()
    }
    fn node_id(&'a self, n: &Nd) -> dot::Id<'a> {
        dot::Id::new(format!("N{}", n.0)).unwrap()
    }
    fn node_label<'b>(&'b self, n: &Nd) -> dot::LabelText<'b> {
        if n.0 == u32::max_value() {
            dot::LabelText::LabelStr("root".into())
        } else {
            let scope = &self.scopes[n.to_usize()];
            let vars: Vec<String> = scope.variables.iter().map(|v| format!("{}", v)).collect();
            dot::LabelText::LabelStr(format!("SId {}\n{}", n, vars.join(", ")).into())
        }
    }
    fn edge_label<'b>(&'b self, _: &Ed) -> dot::LabelText<'b> {
        dot::LabelText::LabelStr("".into())
    }
}

impl<'a> dot::GraphWalk<'a, Nd, Ed> for &HierarchicalPrefix {
    fn nodes(&'a self) -> dot::Nodes<'a, Nd> {
        let mut nodes: Vec<Nd> = self.scopes.iter().map(|s| s.id).collect();
        nodes.push(ScopeId::new(u32::max_value() as usize)); // dummy root node
        nodes.into()
    }
    fn edges(&'a self) -> dot::Edges<'a, Ed> {
        let mut edges: Vec<Ed> = self
            .next_scopes
            .iter()
            .enumerate()
            .flat_map(|(i, next)| {
                next.iter()
                    .map(|&j| (ScopeId::new(i), j))
                    .collect::<Vec<Ed>>()
            })
            .collect();
        // root node
        self.roots.iter().for_each(|&root| {
            edges.push((ScopeId::new(u32::max_value() as usize), root));
        });
        edges.into()
    }
    fn source(&self, e: &Ed) -> Nd {
        e.0
    }
    fn target(&self, e: &Ed) -> Nd {
        e.1
    }
}

// Dot representation
impl HierarchicalPrefix {
    #[allow(dead_code)]
    pub(crate) fn print_dot_repr(&self) {
        dot::render(&self, &mut std::io::stdout()).unwrap_or_else(|e| println!("{}", e));
    }
}
