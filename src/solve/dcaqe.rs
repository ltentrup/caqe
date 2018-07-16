extern crate cryptominisat;
use self::cryptominisat::*;

use super::super::*;

#[cfg(feature = "statistics")]
use super::super::utils::statistics::TimingStats;

use super::super::parse::dqdimacs;

use super::super::matrix::depenendcy::*;

type DQMatrix = Matrix<DependencyPrefix>;

pub struct DCaqeSolver<'a> {
    matrix: &'a mut DQMatrix,
    result: SolverResult,
    global: GlobalSolverData,
    levels: Vec<SolverLevel>,
}

impl<'a> DCaqeSolver<'a> {
    pub fn new(matrix: &mut DQMatrix) -> DCaqeSolver {
        // make sure every scope is contained where variables
        // may be introduced by fork extension
        matrix.prefix.build_closure();
        let (levels, global) = Self::build_abstraction(matrix);
        DCaqeSolver {
            matrix,
            result: SolverResult::Unknown,
            global,
            levels,
        }
    }

    /// Builds the core data structure for the algorithm
    ///
    /// In detail, the function
    /// - builds the antichain decomposition of the lattice representing the partial order induced by the dependencies
    /// - determines at which abstraction which universal variable has to be introduced
    fn build_abstraction(matrix: &mut DQMatrix) -> (Vec<SolverLevel>, GlobalSolverData) {
        let antichains = matrix.prefix.antichain_decomposition();

        let mut abstractions: Vec<SolverLevel> = Vec::new();
        let mut global = GlobalSolverData::new(matrix);

        let mut bound_universals = FxHashSet::default();
        for antichain in antichains.iter() {
            let universals = antichain
                .iter()
                .fold(FxHashSet::default(), |val, &scope_id| {
                    let scope = &matrix.prefix.scopes[scope_id];
                    val.union(&scope.dependencies).map(|x| *x).collect()
                })
                .difference(&bound_universals)
                .map(|x| *x)
                .collect();
            bound_universals = bound_universals.union(&universals).map(|x| *x).collect();

            if !universals.is_empty() {
                let level = abstractions.len();
                debug!("universal level {}: {:?}", level, universals);
                for &var in &universals {
                    global.level_lookup.insert(var, level);
                }
                abstractions.push(SolverLevel::Universal(Abstraction::new_universal(
                    matrix,
                    &universals,
                    &global.level_lookup,
                    level,
                )));
            }
            let level = abstractions.len();
            abstractions.push(SolverLevel::Existential(
                antichain
                    .iter()
                    .map(|&scope_id| {
                        let scope = &matrix.prefix.scopes[scope_id];
                        debug!("existential level {}: {:?}", level, scope);
                        for &var in &scope.existentials {
                            global.level_lookup.insert(var, level);
                        }
                        Abstraction::new_existential(matrix, scope_id, scope, level)
                    })
                    .collect(),
            ))
        }
        (abstractions, global)
    }

    fn update_abstractions(&mut self, clauses: Vec<ClauseId>, variables: Vec<Variable>) {
        trace!("update_abstractions");

        for &variable in &variables {
            let scope_id = self.matrix
                .prefix
                .variables()
                .get(variable)
                .get_scope_id()
                .expect("every newly created variable is existential");

            'outer: for (i, level) in self.levels.iter_mut().enumerate() {
                match level {
                    SolverLevel::Existential(abstractions) => {
                        for abstraction in abstractions.iter_mut() {
                            if abstraction.scope_id.unwrap() == scope_id {
                                // found match
                                self.global.level_lookup.insert(variable, i);
                                abstraction.add_variable(variable);
                                break 'outer;
                            }
                        }
                    }
                    _ => continue,
                }
            }
        }

        for level in self.levels.iter_mut() {
            if let SolverLevel::Universal(abstraction) = level {
                abstraction.reset();
            }
        }
        // TODO: reset skolem functions

        self.global.unsat_core.grow(clauses.len(), false);

        for level in self.levels.iter_mut() {
            level.add_clauses(&self.matrix, &self.global.level_lookup, &clauses);
        }
    }
}

#[derive(Debug, PartialEq)]
enum SolveLevelResult {
    ContinueInner,
    /// A conflict for the existential player, with conflict clause
    UnsatConflict(Clause),
    /// A conflict for the universal player, with originating level
    SatConflict(usize),
}

impl<'a> super::Solver for DCaqeSolver<'a> {
    fn solve(&mut self) -> SolverResult {
        trace!("solve");

        let mut level = 0;
        loop {
            let result = match self.levels[level] {
                SolverLevel::Universal(ref mut abstraction) => {
                    match abstraction.solve(&mut self.matrix, &mut self.global) {
                        AbstractionResult::CandidateFound => {
                            // continue with inner level
                            SolveLevelResult::ContinueInner
                        }
                        AbstractionResult::CandidateRefuted => SolveLevelResult::SatConflict(level),
                        _ => unreachable!(),
                    }
                }
                SolverLevel::Existential(ref mut abstractions) => {
                    let len = abstractions.len();
                    let mut result = SolveLevelResult::ContinueInner;
                    for abstraction in abstractions {
                        match abstraction.solve(&mut self.matrix, &mut self.global) {
                            AbstractionResult::CandidateRefuted => {
                                // global.unsat_core represents the conflict clause
                                let clause = self.global.build_conflict_clause(
                                    &self.matrix,
                                    abstraction.scope_id.unwrap(),
                                );
                                result = SolveLevelResult::UnsatConflict(clause);
                                break;
                            }
                            AbstractionResult::CandidateVerified => {
                                assert!(len == 1);
                                result = SolveLevelResult::SatConflict(level);
                                break;
                            }
                            AbstractionResult::CandidateFound => {
                                debug_assert!(result == SolveLevelResult::ContinueInner);
                            }
                        }
                    }
                    result
                }
            };
            match result {
                SolveLevelResult::ContinueInner => level = level + 1,
                SolveLevelResult::UnsatConflict(clause) => {
                    if clause.len() == 0 {
                        // derived the empty clause
                        return SolverResult::Unsatisfiable;
                    }
                    debug!("conflict clause is {}", clause.dimacs());
                    match self.global
                        .dependency_conflict_resolution(&mut self.matrix, clause)
                    {
                        Ok((clauses, variables)) => {
                            // we applied dependency conflict resolution
                            self.update_abstractions(clauses, variables);
                            level = 0;
                        }
                        Err(scope_id) => {
                            // we apply standard conflict resolution
                            // go to level with scope_id, refine, and proceed
                            level = level - 1;
                            loop {
                                match &mut self.levels[level] {
                                    SolverLevel::Existential(abstractions) => {
                                        // refine and proceed with this level
                                        let mut refined = false;
                                        for abstraction in abstractions {
                                            if abstraction.scope_id.unwrap() == scope_id {
                                                // found the existential level to refine
                                                abstraction.refine(&self.global.unsat_core);
                                                refined = true;
                                            }
                                        }
                                        if !refined {
                                            level = level - 1;
                                        } else {
                                            break;
                                        }
                                    }
                                    SolverLevel::Universal(abstraction) => {
                                        // optimize and proceed with inner level
                                        abstraction.unsat_propagation(&mut self.global);
                                        level = level - 1;
                                    }
                                }
                            }
                        }
                    }
                }
                SolveLevelResult::SatConflict(orig_level) => {
                    loop {
                        match &mut self.levels[level] {
                            SolverLevel::Existential(abstractions) => {
                                // optimize and proceed with inner level
                                if level == 0 {
                                    return SolverResult::Satisfiable;
                                }
                                for abstraction in abstractions {
                                    abstraction.entry_minimization(&self.matrix, &mut self.global);
                                }
                                level = level - 1;
                            }
                            SolverLevel::Universal(abstraction) => {
                                // refine and proceed with this level
                                if level < orig_level {
                                    abstraction.refine(&self.global.unsat_core);
                                    break;
                                } else if level == 0 {
                                    return SolverResult::Satisfiable;
                                } else {
                                    level = level - 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

enum SolverLevel {
    Universal(Abstraction),
    Existential(Vec<Abstraction>),
}

impl SolverLevel {
    fn add_clauses(
        &mut self,
        matrix: &DQMatrix,
        level_lookup: &FxHashMap<Variable, usize>,
        clauses: &[ClauseId],
    ) {
        match self {
            SolverLevel::Universal(abstraction) => {
                abstraction.add_clauses(matrix, level_lookup, clauses)
            }
            SolverLevel::Existential(abstractions) => {
                for abstraction in abstractions.iter_mut() {
                    abstraction.add_clauses(matrix, level_lookup, clauses)
                }
            }
        }
    }
}

struct GlobalSolverData {
    /// the current assignment
    assignments: FxHashMap<Variable, bool>,

    /// an mapping from variables to the level they are bound
    level_lookup: FxHashMap<Variable, usize>,

    /// representation of an unsatisfiable core as vector of clause ids
    unsat_core: BitVec,
}

impl GlobalSolverData {
    fn new(matrix: &DQMatrix) -> GlobalSolverData {
        GlobalSolverData {
            assignments: FxHashMap::default(),
            level_lookup: FxHashMap::default(),
            unsat_core: BitVec::from_elem(matrix.clauses.len(), false),
        }
    }

    fn build_conflict_clause(&mut self, matrix: &DQMatrix, scope_id: ScopeId) -> Clause {
        let scope = &matrix.prefix.scopes[scope_id];
        let mut literals = Vec::new();
        for (clause_id, _) in self.unsat_core.iter().enumerate().filter(|(_, val)| *val) {
            let clause = &matrix.clauses[clause_id];
            literals.extend(clause.iter().filter(|l| {
                !scope.existentials.contains(&l.variable())
                    && matrix.prefix.depends_on_scope(scope, l.variable())
            }));
        }

        Clause::new(literals)
    }

    fn dependency_conflict_resolution(
        &mut self,
        matrix: &mut DQMatrix,
        conflict_clause: Clause,
    ) -> Result<(Vec<ClauseId>, Vec<Variable>), ScopeId> {
        let mut maximal_scopes: MaxElements<Scope> = MaxElements::new();
        for &literal in conflict_clause.iter() {
            let info = matrix.prefix.variables().get(literal.variable());
            if let &Some(scope_id) = info.get_scope_id() {
                // TODO: we need a clone here, since the prefix is modified below, but this is wasteful
                let scope = matrix.prefix.get_scope(scope_id).clone();
                maximal_scopes.add(scope);
            }
        }
        debug_assert!(maximal_scopes.len() > 0, "clause should not be empty");
        if maximal_scopes.len() == 1 {
            let scope = maximal_scopes.remove(0);
            return Err(matrix.prefix.scope_lookup(&scope.dependencies).unwrap());
        }
        debug!("dependency conflict detected");

        let mut arbiters = Vec::new();
        let mut clauses = Vec::new();

        let mut remaining = conflict_clause;
        let mut meets: MaxElements<Scope> = MaxElements::new();

        while maximal_scopes.len() > 1 {
            // get maximal scope with only one interesction with other scope
            // if this is not possible, there is a dependency cycle

            let index = maximal_scopes
                .get_first(|scope| {
                    meets.clear();
                    for other in maximal_scopes.iter() {
                        if scope == other {
                            continue;
                        }
                        let intersection = scope
                            .dependencies
                            .intersection(&other.dependencies)
                            .map(|x| *x)
                            .collect();
                        meets.add(Scope::new(&intersection));
                    }
                    meets.len() == 1
                })
                .expect("detected a dependency cycle");
            let scope = maximal_scopes.remove(index);
            debug_assert!(meets.len() == 1);
            let meet = meets.iter().next().unwrap();
            debug!("split with {:?} and meet {:?}", scope, meet);

            let arbiter = matrix.prefix.variables().next_unused();
            matrix.prefix.add_existential(arbiter, &meet.dependencies);
            arbiters.push(arbiter);

            // put every literal in splitted clause that
            // (1) is a subset of maximal element
            // (2) is not a subset of meet
            let mut literals: Vec<Literal> = remaining
                .iter()
                .filter(|&literal| {
                    let info = matrix.prefix.variables().get(literal.variable());
                    if let &Some(scope_id) = info.get_scope_id() {
                        let other = &matrix.prefix.scopes[scope_id as usize];
                        other.dependencies.is_subset(&scope.dependencies)
                            && !other.dependencies.is_subset(&meet.dependencies)
                    } else {
                        // universal variable
                        scope.dependencies.contains(&literal.variable())
                    }
                })
                .map(|x| *x)
                .collect();
            literals.push(Literal::new(arbiter, true));

            let splitted = Clause::new(literals);

            // put every literal into remaining clause that
            // (1) is not a subset of maximal element
            // (2) is a subset of meet
            let mut literals: Vec<Literal> = remaining
                .iter()
                .filter(|&literal| {
                    let info = matrix.prefix.variables().get(literal.variable());
                    if let &Some(scope_id) = info.get_scope_id() {
                        let other = &matrix.prefix.scopes[scope_id as usize];
                        !other.dependencies.is_subset(&scope.dependencies)
                            || other.dependencies.is_subset(&meet.dependencies)
                    } else {
                        // universal variable not in difference of maximal element and meet
                        !(scope.dependencies.contains(&literal.variable())
                            && !meet.dependencies.contains(&literal.variable()))
                    }
                })
                .map(|x| *x)
                .collect();
            literals.push(Literal::new(arbiter, false));
            remaining = Clause::new(literals);

            debug!(
                "arbiter {}, clause {} and {}",
                arbiter,
                splitted.dimacs(),
                remaining.dimacs()
            );

            clauses.push(splitted);
        }

        clauses.push(remaining);

        debug!(
            "added {} clauses and {} variables",
            clauses.len(),
            arbiters.len()
        );

        let clauses = clauses
            .into_iter()
            .map(|clause| matrix.add(clause))
            .collect();

        if log_enabled!(Level::Debug) {
            debug!("\n{}", matrix.dimacs());
        }

        Ok((clauses, arbiters))
    }
}

#[derive(Debug, PartialEq, Eq)]
enum AbstractionResult {
    CandidateFound,
    CandidateRefuted,

    /// base case of recursion
    CandidateVerified,
}

struct Abstraction {
    sat: cryptominisat::Solver,
    variable_to_sat: FxHashMap<Variable, Lit>,
    t_literals: Vec<(ClauseId, Lit)>,
    b_literals: Vec<(ClauseId, Lit)>,

    /// stores for every clause whether the clause is satisfied or not by assignments to outer variables
    entry: BitVec,

    /// Stores the clauses for which the current level is maximal, i.e.,
    /// there is no literal of an inner scope contained.
    /// For universal scopes, it stores the clauses which are only influenced by
    /// the current, or some inner, scope.
    max_clauses: BitVec,

    /// lookup from sat solver variables to clause id's
    reverse_t_literals: FxHashMap<u32, ClauseId>,

    /// stores the assumptions given to sat solver
    sat_solver_assumptions: Vec<Lit>,

    /// sat literal to implement incremental sat solving
    inc_sat_lit: Option<Lit>,

    level: usize,
    is_max_level: bool,

    /// scope_id for existential scopes, `None` for universal ones
    scope_id: Option<ScopeId>,
}

impl Abstraction {
    fn new(matrix: &DQMatrix, level: usize, scope_id: Option<ScopeId>) -> Abstraction {
        let mut sat = cryptominisat::Solver::new();
        sat.set_num_threads(1);
        let is_max_level = scope_id
            .map(|scope_id| {
                let scope = &matrix.prefix.scopes[scope_id];
                matrix.prefix.is_maximal(scope)
            })
            .unwrap_or(false);
        Abstraction {
            sat,
            variable_to_sat: FxHashMap::default(),
            b_literals: Vec::new(),
            t_literals: Vec::new(),
            reverse_t_literals: FxHashMap::default(),
            entry: BitVec::from_elem(matrix.clauses.len(), false),
            max_clauses: BitVec::from_elem(matrix.clauses.len(), false),
            sat_solver_assumptions: Vec::new(),
            inc_sat_lit: None,
            level,
            is_max_level,
            scope_id,
        }
    }

    fn new_universal(
        matrix: &DQMatrix,
        variables: &FxHashSet<Variable>,
        level_lookup: &FxHashMap<Variable, usize>,
        level: usize,
    ) -> Abstraction {
        // build SAT instance for negation of clauses, i.e., basically we only build binary clauses
        debug_assert!(!variables.is_empty());

        let mut abs = Self::new(matrix, level, None);

        // add variables of scope to sat solver
        for &variable in variables {
            abs.variable_to_sat.insert(variable, abs.sat.new_var());
        }

        for (clause_id, clause) in matrix.clauses.iter().enumerate() {
            abs.encode_universal_clause(matrix, clause_id as ClauseId, clause, level_lookup);
        }

        abs.inc_sat_lit = Some(abs.sat.new_var());

        abs
    }

    fn encode_universal_clause(
        &mut self,
        matrix: &DQMatrix,
        clause_id: ClauseId,
        clause: &Clause,
        level_lookup: &FxHashMap<Variable, usize>,
    ) {
        debug_assert!(clause.len() != 0, "unit clauses indicate a problem");

        let mut need_b_lit = false;
        let mut need_t_lit = false;

        let mut sat_var = None;
        for &literal in clause.iter() {
            if !self.variable_to_sat.contains_key(&literal.variable()) {
                if level_lookup.contains_key(&literal.variable()) {
                    // bound outer, otherwise would not contained in level_lookup yet
                    need_t_lit = true;
                }
                continue;
            }
            let sat_var = *sat_var.get_or_insert_with(|| self.sat.new_var());
            let lit = self.lit_to_sat_lit(literal);
            self.sat.add_clause(&[!sat_var, !lit]);
            need_b_lit = true;
        }

        if !need_b_lit {
            // no variable of current scope
            return;
        }

        let sat_var = sat_var.expect("sat_var cannot be empty at this point");

        if need_t_lit {
            self.t_literals.push((clause_id, sat_var));
            debug_assert!(!self.reverse_t_literals.contains_key(&sat_var.var()));
            self.reverse_t_literals.insert(sat_var.var(), clause_id);
        }

        if need_b_lit {
            self.b_literals.push((clause_id, sat_var));
        }

        if !need_t_lit && need_b_lit {
            // there is no outer influence on clause
            self.max_clauses.set(clause_id as usize, true);
        }
    }

    fn new_existential(
        matrix: &DQMatrix,
        scope_id: ScopeId,
        scope: &Scope,
        level: usize,
    ) -> Abstraction {
        let mut abs = Self::new(matrix, level, Some(scope_id));
        let mut sat_clause = Vec::new();

        // add variables of scope to sat solver
        for &variable in scope.existentials.iter() {
            abs.variable_to_sat.insert(variable, abs.sat.new_var());
        }

        for (clause_id, clause) in matrix.clauses.iter().enumerate() {
            abs.encode_existential_clause(
                matrix,
                clause_id as ClauseId,
                clause,
                &mut sat_clause,
                scope,
            );
        }

        debug!("Scope {}", scope_id);
        debug!("t-literals: {}", abs.t_literals.len());
        debug!("b-literals: {}", abs.b_literals.len());

        abs
    }

    fn encode_existential_clause(
        &mut self,
        matrix: &DQMatrix,
        clause_id: ClauseId,
        clause: &Clause,
        sat_clause: &mut Vec<Lit>,
        scope: &Scope,
    ) {
        debug_assert!(clause.len() != 0, "unit clauses indicate a problem");
        debug_assert!(sat_clause.is_empty());

        let mut need_b_lit = false;
        let mut need_t_lit = false;
        let mut contains_variables = false;
        let mut maximal_elements: MaxElements<&Scope> = MaxElements::new();

        for &literal in clause.iter() {
            if !self.variable_to_sat.contains_key(&literal.variable()) {
                // not of current scope
                let info = matrix.prefix.variables().get(literal.variable());
                if let &Some(scope_id) = info.get_scope_id() {
                    // existential variable
                    debug_assert!(scope_id != self.scope_id.unwrap());
                    let other_scope = matrix.prefix.get_scope(scope_id);
                    if other_scope.dependencies.is_subset(&scope.dependencies) {
                        maximal_elements.add(other_scope);
                        need_t_lit = true;
                    } else {
                        need_b_lit = true;
                    }
                } else {
                    // universal variable
                    if scope.dependencies.contains(&literal.variable()) {
                        need_t_lit = true;
                    }
                }
                continue;
            }
            contains_variables = true;
            sat_clause.push(self.lit_to_sat_lit(literal));
        }

        if !contains_variables && maximal_elements.len() < 2 {
            debug_assert!(sat_clause.is_empty());
            return;
        }

        if need_t_lit {
            // we need a t-literal if there are at least two, inner and incomparable scopes directly above
            let t_lit = self.sat.new_var();
            sat_clause.push(t_lit);
            self.t_literals.push((clause_id as ClauseId, t_lit));
            self.reverse_t_literals
                .insert(t_lit.var(), clause_id as ClauseId);
        }

        if need_b_lit {
            debug_assert!(need_b_lit);
            let b_lit = self.sat.new_var();
            sat_clause.push(!b_lit);
            self.b_literals.push((clause_id as ClauseId, b_lit));
        }

        debug_assert!(!sat_clause.is_empty());
        self.sat.add_clause(sat_clause.as_ref());
        sat_clause.clear();

        if !need_b_lit {
            // clause has no inner influence
            self.max_clauses.set(clause_id as usize, true);
        }
    }

    fn add_variable(&mut self, variable: Variable) {
        self.variable_to_sat.insert(variable, self.sat.new_var());
    }

    fn add_clauses(
        &mut self,
        matrix: &DQMatrix,
        level_lookup: &FxHashMap<Variable, usize>,
        clauses: &[ClauseId],
    ) {
        self.entry.grow(clauses.len(), false);
        self.max_clauses.grow(clauses.len(), false);

        let mut sat_clause = Vec::new();

        for &clause_id in clauses {
            let clause = &matrix.clauses[clause_id as usize];
            if self.is_universal() {
                self.encode_universal_clause(matrix, clause_id, clause, level_lookup);
            } else {
                let scope = matrix.prefix.get_scope(self.scope_id.unwrap());
                self.encode_existential_clause(matrix, clause_id, clause, &mut sat_clause, scope);
            }
        }
    }

    fn lit_to_sat_lit(&self, literal: Literal) -> Lit {
        let lit = self.variable_to_sat[&literal.variable()];
        if literal.signed() {
            !lit
        } else {
            lit
        }
    }

    fn is_universal(&self) -> bool {
        self.scope_id.is_none()
    }

    fn variable_is_dependency(
        &self,
        var: Variable,
        matrix: &DQMatrix,
        global: &GlobalSolverData,
    ) -> bool {
        if let Some(scope_id) = self.scope_id {
            // existential scope
            // only variables scope depends on
            let scope = &matrix.prefix.scopes[scope_id];
            if scope.existentials.contains(&var) {
                false
            } else {
                matrix.prefix.depends_on_scope(scope, var)
            }
        } else {
            debug_assert!(self.is_universal());
            // everything bound earlier is relevant
            let var_level = global.level_lookup[&var];
            var_level < self.level
        }
    }

    fn check_candidate_exists(
        &mut self,
        matrix: &DQMatrix,
        global: &mut GlobalSolverData,
    ) -> Lbool {
        trace!("check_candidate_exists");

        self.entry.clear();

        // we compute the entry as a projection of the current assignment on the matrix
        // with the restriction that the variable is `visible` for the scope
        debug!("relevant assignments");
        for (&var, &value) in &global.assignments {
            if !self.variable_is_dependency(var, matrix, global) {
                continue;
            }
            debug!("{} {}", var, value);

            let literal = Literal::new(var, !value);
            for &clause_id in matrix.occurrences(literal) {
                self.entry.set(clause_id as usize, true);
            }
        }

        self.sat_solver_assumptions.clear();

        #[cfg(debug_assertions)]
        let mut debug_print = String::new();

        // we iterate in parallel over the entry and the t-literals of current level
        // there are 3 possibilities:
        // * clause from entry is not a t-lit: push entry to next quantifier
        // * clause is in entry and a t-lit: assume positively
        // * clause is not in entry and a t-lit: assume negatively
        for &(clause_id, mut t_literal) in self.t_literals.iter() {
            if !self.entry[clause_id as usize] {
                t_literal = !t_literal;
            }
            if self.is_universal() {
                t_literal = !t_literal;
            }

            #[cfg(debug_assertions)]
            {
                if t_literal.isneg() {
                    debug_print.push_str(&format!(" -t{}", clause_id));
                } else {
                    debug_print.push_str(&format!(" t{}", clause_id));
                }
            }

            if self.is_universal() && !t_literal.isneg() {
                // assume t-literal completely for existential quantifier
                // and only negatively for universal quantifier
                continue;
            }

            self.sat_solver_assumptions.push(t_literal);
        }

        #[cfg(debug_assertions)]
        debug!("assume {}", debug_print);

        if let Some(inc_lit) = self.inc_sat_lit {
            self.sat_solver_assumptions.push(!inc_lit);
        }

        self.sat
            .solve_with_assumptions(self.sat_solver_assumptions.as_ref())
    }

    fn update_assignment(&mut self, global: &mut GlobalSolverData) {
        trace!("update_assignment");

        #[cfg(debug_assertions)]
        let mut debug_print = String::new();

        let model = self.sat.get_model();
        for (&variable, &sat_var) in self.variable_to_sat.iter() {
            let value = match model[sat_var.var() as usize] {
                Lbool::True => true,
                Lbool::False => false,
                _ => panic!("expect all variables to be assigned"),
            };

            #[cfg(debug_assertions)]
            {
                if value {
                    debug_print.push_str(&format!(" {}", variable));
                } else {
                    debug_print.push_str(&format!(" -{}", variable));
                }
            }

            let entry = global.assignments.entry(variable).or_insert(value);
            *entry = value;
        }

        #[cfg(debug_assertions)]
        debug!("assignment {}", debug_print);
    }

    fn get_unsat_core(&mut self, global: &mut GlobalSolverData) {
        trace!("unsat_core");

        global.unsat_core.clear();

        #[cfg(debug_assertions)]
        let mut debug_print = String::new();

        let failed = self.sat.get_conflict();
        for l in failed {
            if let Some(inc_sat) = self.inc_sat_lit {
                // ignore incremental sat literal
                if l.var() == inc_sat.var() {
                    continue;
                }
            }
            let clause_id = self.reverse_t_literals[&l.var()];
            global.unsat_core.set(clause_id as usize, true);

            #[cfg(debug_assertions)]
            debug_print.push_str(&format!(" t{}", clause_id));
        }

        #[cfg(debug_assertions)]
        debug!("unsat core: {}", debug_print);
    }

    fn entry_minimization(&self, matrix: &DQMatrix, global: &mut GlobalSolverData) {
        trace!("entry_minimization");

        let scope = matrix
            .prefix
            .get_scope(self.scope_id.expect("only for existential abstractions"));

        // add clauses to entry where the current scope is maximal
        global.unsat_core.union(&self.max_clauses);

        for variable in scope.existentials.iter() {
            let value = global.assignments[variable];
            let literal = Literal::new(*variable, !value);

            // check if assignment satisfied clause in unsat core
            // if yes, it can be removed
            for &clause_id in matrix.occurrences(literal) {
                if global.unsat_core[clause_id as usize] {
                    //needed = true;
                    global.unsat_core.set(clause_id as usize, false);
                }
            }

            /*
            // unsound if values are fixed by skolem function
            if !needed {
                // the current value set is not needed for the entry, try other polarity
                for &clause_id in matrix.occurrences(-literal) {
                    if global.unsat_core[clause_id as usize] {
                        global.unsat_core.set(clause_id as usize, false);
                    }
                }
            }*/
        }
    }

    fn add_b_lit_and_adapt_abstraction(
        clause_id: ClauseId,
        sat: &mut cryptominisat::Solver,
        b_literals: &Vec<(ClauseId, Lit)>,
        t_literals: &mut Vec<(ClauseId, Lit)>,
        reverse_t_literals: &mut FxHashMap<u32, Variable>,
    ) -> Lit {
        // first check if there is a b-literal for clause
        // if yes, just return it (the currents scope influences clause since there is at least one variable contained)
        // if no, we continue
        match b_literals.binary_search_by(|elem| elem.0.cmp(&clause_id)) {
            Ok(pos) => return b_literals[pos].1,
            Err(_) => {}
        };

        // we then check, if there is a corresponding t-literal
        // if yes, we return this instead
        // if no, we have to adapt the abstraction by inserting a new t-literal
        let insert_pos = match t_literals.binary_search_by(|elem| elem.0.cmp(&clause_id)) {
            Ok(pos) => return t_literals[pos].1,
            Err(pos) => pos,
        };
        let sat_lit = sat.new_var();
        t_literals.insert(insert_pos, (clause_id, sat_lit));
        reverse_t_literals.insert(sat_lit.var(), clause_id);

        // note that, we could also adapt b_literals (with the same sat_literal)
        // however, this is not necessary and not directly obvious
        // 1) reason *not* to do it: in get_assumptions we iterate over b_literals to check
        //    if we can improve the assumptions produced by the SAT solver. Since the clauses
        //    that are added here have no influence of current scope, this check is wasted time
        // 2) we do not *need* them, because abstraction entries are just copied from one
        //    scope to another

        sat_lit
    }

    /// filters those clauses that are only influenced by this quantifier (or inner)
    fn unsat_propagation(&self, global: &mut GlobalSolverData) {
        trace!("unsat_propagation");
        global.unsat_core.difference(&self.max_clauses);
    }

    fn refine(&mut self, learned: &BitVec) {
        trace!("refine");

        let blocking_clause = &mut self.sat_solver_assumptions;
        blocking_clause.clear();

        #[cfg(debug_assertions)]
        let mut debug_print = String::new();

        for (clause_id, _) in learned.iter().enumerate().filter(|(_, val)| *val) {
            let b_lit = Self::add_b_lit_and_adapt_abstraction(
                clause_id as ClauseId,
                &mut self.sat,
                &self.b_literals,
                &mut self.t_literals,
                &mut self.reverse_t_literals,
            );
            blocking_clause.push(b_lit);

            #[cfg(debug_assertions)]
            debug_print.push_str(&format!(" b{}", clause_id));
        }

        if let Some(inc_lit) = self.inc_sat_lit {
            blocking_clause.push(inc_lit);
        }

        self.sat.add_clause(blocking_clause.as_ref());

        #[cfg(debug_assertions)]
        debug!("refinement: {}", debug_print);
    }

    /// Resets the abstraction completely, i.e., removes all learnt clauses.
    /// Only applicable for universal levels.
    fn reset(&mut self) {
        debug_assert!(self.is_universal());
        if let Some(inc_lit) = self.inc_sat_lit {
            self.sat.add_clause(&vec![inc_lit]);
        }
        self.inc_sat_lit = Some(self.sat.new_var());
    }

    fn solve(&mut self, matrix: &DQMatrix, global: &mut GlobalSolverData) -> AbstractionResult {
        trace!("solve");

        debug!("");
        info!("solve level {}", self.level);
        if let Some(scope_id) = self.scope_id {
            let scope = matrix.prefix.get_scope(scope_id);
            debug!("{:?}", scope);
        }

        match self.check_candidate_exists(matrix, global) {
            Lbool::True => {
                // there is a candidate solution that needs to be verified
                self.update_assignment(global);

                if self.is_max_level {
                    AbstractionResult::CandidateVerified
                } else {
                    AbstractionResult::CandidateFound
                }
            }
            Lbool::False => {
                // there is no candidate solution, return witness
                self.get_unsat_core(global);
                AbstractionResult::CandidateRefuted
            }
            _ => unreachable!(),
        }
    }
}

#[derive(Debug)]
struct MaxElements<T>
where
    T: PartialOrd,
{
    elements: Vec<T>,
}

/// This data structure manages a set of maximal, incomparable elements
impl<T> MaxElements<T>
where
    T: PartialOrd,
{
    fn new() -> MaxElements<T> {
        MaxElements {
            elements: Vec::new(),
        }
    }

    /// We remove all elements that are smaller than `element`.
    /// Then, we add `element` if there is no other element that is greater or equal.
    fn add(&mut self, element: T) {
        self.elements.retain(|other| !(other < &element));
        let subsumed = self.elements
            .iter()
            .fold(false, |val, other| val || other >= &element);
        if !subsumed {
            self.elements.push(element);
        }
    }

    fn get_first<P>(&self, mut f: P) -> Option<usize>
    where
        P: FnMut(&T) -> bool,
    {
        self.elements
            .iter()
            .enumerate()
            .filter(|(_, ele)| f(ele))
            .map(|(i, _)| i)
            .next()
    }

    fn remove(&mut self, index: usize) -> T {
        self.elements.remove(index)
    }

    fn len(&self) -> usize {
        self.elements.len()
    }

    fn iter(&self) -> std::slice::Iter<T> {
        self.elements.iter()
    }

    fn clear(&mut self) {
        self.elements.clear();
    }
}

/*impl<T> IntoIterator for MaxElements<T>
where
    T: PartialOrd,
{
    type Item = T;
    type IntoIter = ::std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.elements.into_iter()
    }
}*/

#[cfg(test)]
mod tests {

    use super::*;
    use solve::Solver;

    #[test]
    fn test_max_elements() {
        let mut container = MaxElements::new();
        assert_eq!(container.len(), 0);
        container.add(10);
        assert_eq!(container.len(), 1);
        container.add(3);
        assert_eq!(container.len(), 1);
        container.add(11);
        assert_eq!(container.len(), 1);
    }

    #[test]
    fn test_sat_simple() {
        let instance = "c
p cnf 5 4
a 1 2 0
d 3 1 0
d 4 2 0
e 5 0
3 2 5 0
-3 -2 5 0
4 1 -5 0
-4 -1 -5 0
";
        let mut matrix = dqdimacs::parse(&instance).unwrap();
        let mut solver = DCaqeSolver::new(&mut matrix);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
    }

    #[test]
    fn test_unsat_simple() {
        let instance = "c
p cnf 4 6
a 1 2 0
d 3 1 0
d 4 2 0
3 4 1 0
-3 -4 1 0
3 4 -1 -2 0
-3 4 -1 2 0
3 -4 -1 2 0
-3 -4 -1 -2 0
";
        let mut matrix = dqdimacs::parse(&instance).unwrap();
        let mut solver = DCaqeSolver::new(&mut matrix);
        assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
    }
}
