use super::super::matrix::dependency::*;
use super::super::*;
use bit_vec::BitVec;
use cryptominisat::*;
use log::{debug, error, info, log_enabled, trace};
use rustc_hash::{FxHashMap, FxHashSet};
use simplelog::Level;
use std::cmp::Ordering;

#[cfg(feature = "statistics")]
use super::super::utils::statistics::{CountingStats, TimingStats};

type DQMatrix = Matrix<DependencyPrefix>;

pub struct DCaqeSolver<'a> {
    matrix: &'a mut DQMatrix,
    global: GlobalSolverData,
    levels: Vec<SolverLevel>,
}

impl<'a> DCaqeSolver<'a> {
    pub fn new(matrix: &'a mut DQMatrix, config: &'a DCaqeSpecificSolverConfig) -> DCaqeSolver<'a> {
        // make sure every scope is contained where variables
        // may be introduced by fork extension
        matrix.prefix.build_closure();
        let (levels, global) = Self::build_abstraction(matrix, config);
        DCaqeSolver {
            matrix,
            global,
            levels,
        }
    }

    /// Builds the core data structure for the algorithm
    ///
    /// In detail, the function
    /// - builds the antichain decomposition of the lattice representing the partial order induced by the dependencies
    /// - determines at which abstraction which universal variable has to be introduced
    fn build_abstraction(
        matrix: &mut DQMatrix,
        config: &DCaqeSpecificSolverConfig,
    ) -> (Vec<SolverLevel>, GlobalSolverData) {
        let antichains = matrix.prefix.antichain_decomposition();

        let mut abstractions: Vec<SolverLevel> = Vec::new();
        let mut global = GlobalSolverData::new(matrix, config);

        /*#[cfg(debug_assertions)]
        {
            for clause in &matrix.clauses {
                assert!(!matrix.prefix.contains_dependency_fork(clause));
            }
            println!("no dependency forks initially");
        }*/

        let mut bound_universals = FxHashSet::default();
        for antichain in &antichains {
            let universals = antichain
                .iter()
                .fold(FxHashSet::default(), |val, &scope_id| {
                    let scope = &matrix.prefix.scopes[scope_id];
                    val.union(&scope.dependencies).cloned().collect()
                })
                .difference(&bound_universals)
                .cloned()
                .collect();
            bound_universals = bound_universals.union(&universals).cloned().collect();

            if !universals.is_empty() {
                let level = abstractions.len();
                debug!("universal level {}: {:?}", level, universals);
                for &var in &universals {
                    global.level_lookup.insert(var, level);
                }
                abstractions.push(SolverLevel::Universal(
                    Abstraction::new_universal(matrix, &universals, &global.level_lookup, level)
                        .into(),
                ));
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
                        // we only need to learn Skolem functions if the bound universal variabales are not equal to dependencies
                        let needs_learner = bound_universals != scope.dependencies;
                        Abstraction::new_existential(matrix, scope_id, scope, level, needs_learner)
                    })
                    .collect(),
            ))
        }
        (abstractions, global)
    }

    fn update_abstractions(&mut self, clauses: &[ClauseId], variables: &[Variable]) {
        trace!("update_abstractions");

        for &variable in variables {
            let scope_id = self
                .matrix
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

        for level in &mut self.levels {
            match level {
                SolverLevel::Universal(abstraction) => abstraction.reset(),
                SolverLevel::Existential(abstractions) => {
                    for abstraction in abstractions.iter_mut() {
                        if let Some(l) = abstraction.learner.as_mut() {
                            l.reset()
                        }
                    }
                }
            }
        }

        self.global.unsat_core.grow(clauses.len(), false);

        for level in &mut self.levels {
            level.add_clauses(&self.matrix, &self.global.level_lookup, &clauses);
        }
    }

    fn solve_level(&mut self, level: usize) -> SolveLevelResult {
        match self.levels[level] {
            SolverLevel::Universal(ref mut abstraction) => {
                match abstraction.solve(&self.matrix, &mut self.global) {
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
                    match abstraction.solve(&self.matrix, &mut self.global) {
                        AbstractionResult::CandidateRefuted => {
                            // `global.unsat_core` represents the conflict clause
                            let level = self.global.get_unsat_level(&self.matrix, level);
                            result = SolveLevelResult::UnsatConflict(level);
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
        }
    }

    fn process_level_result(
        &mut self,
        mut level: usize,
        result: SolveLevelResult,
    ) -> Result<usize, SolverResult> {
        #[cfg(feature = "statistics")]
        let _timer = self
            .global
            .timings
            .start(GlobalSolverEvents::ProcessLevelResult);

        match result {
            SolveLevelResult::ContinueInner => level += 1,
            SolveLevelResult::UnsatConflict(target_level) => {
                let target_level = if let Some(l) = target_level {
                    l
                } else {
                    // derived the empty clause
                    covered_by!("unsat_universal_reduction");
                    return Err(SolverResult::Unsatisfiable);
                };
                debug_assert!(target_level < level);

                // go to target level
                level -= 1;
                while level > target_level {
                    match &mut self.levels[level] {
                        SolverLevel::Existential(_abstractions) => {
                            // skip level since there is no influence on unsat core
                            level -= 1;
                        }
                        SolverLevel::Universal(abstraction) => {
                            // optimize and proceed with inner level
                            abstraction.unsat_propagation(&mut self.global);
                            level -= 1;
                        }
                    }
                }
                debug_assert!(level == target_level);

                let mut clause = self.global.build_conflict_clause(&self.matrix, level);
                debug_assert!(clause.len() > 0, "empty clauses are handeled before");
                debug!("conflict clause is {}", clause.dimacs());

                let len_before = clause.len();
                // are there still non-dependencies in clause?
                self.matrix.prefix.reduce_universal(&mut clause);
                let universally_reduced = len_before != clause.len();

                match self.global.dependency_conflict_resolution(
                    &mut self.matrix,
                    clause,
                    universally_reduced,
                ) {
                    DepConfResResult::Split(clauses, variables) => {
                        // we applied dependency conflict resolution
                        self.update_abstractions(&clauses, &variables);

                        self.lattice_expansion(&variables, level);

                        level = 0;
                    }
                    DepConfResResult::Refine(scope_id) => {
                        // we apply standard conflict resolution
                        // go to abstraction with scope_id, refine, and proceed

                        let matrix = &self.matrix;

                        match &mut self.levels[level] {
                            SolverLevel::Existential(abstractions) => {
                                // refine and proceed with this level
                                for abstraction in abstractions {
                                    if abstraction.scope_id.unwrap() == scope_id {
                                        // found the existential level to refine
                                        abstraction.refine(&self.global.unsat_core);
                                        Self::standard_expansion(
                                            &mut self.global,
                                            matrix,
                                            abstraction,
                                        );
                                    }
                                }
                            }
                            _ => unreachable!(),
                        }
                    }
                    DepConfResResult::Cycle => {
                        error!("Detected a dependency cycle");
                        return Err(SolverResult::Unknown);
                    }
                }
            }
            SolveLevelResult::SatConflict(orig_level) => {
                loop {
                    match &mut self.levels[level] {
                        SolverLevel::Existential(abstractions) => {
                            // optimize and proceed with inner level
                            if level == 0 {
                                return Err(SolverResult::Satisfiable);
                            }
                            for abstraction in abstractions {
                                abstraction.entry_minimization(&self.matrix, &mut self.global);
                            }
                            level -= 1;
                        }
                        SolverLevel::Universal(abstraction) => {
                            // refine and proceed with this level
                            if level < orig_level {
                                abstraction.refine(&self.global.unsat_core);
                                break;
                            } else if level == 0 {
                                return Err(SolverResult::Satisfiable);
                            } else {
                                level -= 1;
                            }
                        }
                    }
                }
            }
        }
        Ok(level)
    }

    fn lattice_expansion(&mut self, variables: &[Variable], level: usize) {
        if !self.global.config.expansion_refinement {
            return;
        }
        let mut scopes: Vec<ScopeId> = variables
            .iter()
            .map(|var| {
                self.matrix
                    .prefix
                    .variables()
                    .get(*var)
                    .get_scope_id()
                    .expect("arbiters are existential variables")
            })
            .collect();
        scopes.dedup();
        for scope_id in scopes {
            // filter universal variables on larger levels
            let scope = self.matrix.prefix.get_scope(scope_id);
            let universal_assignment: FxHashMap<Variable, bool> = self
                .global
                .assignments
                .iter()
                .filter_map(|(&var, &val)| {
                    if self.matrix.prefix.variables().get(var).is_universal()
                        && !scope.dependencies.contains(&var)
                    {
                        Some((var, val))
                    } else {
                        None
                    }
                })
                .collect();
            if !universal_assignment.is_empty() {
                #[cfg(feature = "statistics")]
                self.global
                    .statistics
                    .inc(GlobalSolverEvents::ExpansionRefinements);
                match &mut self.levels[level] {
                    SolverLevel::Existential(abstractions) => {
                        for abstraction in abstractions {
                            if abstraction.scope_id.unwrap() == scope_id {
                                abstraction.expansion_refinement(
                                    &self.matrix,
                                    &universal_assignment,
                                    &self.global.level_lookup,
                                );
                                break;
                            }
                        }
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    fn standard_expansion(
        global: &mut GlobalSolverData,
        matrix: &DQMatrix,
        abstraction: &mut Abstraction,
    ) {
        if !global.config.expansion_refinement {
            return;
        }
        // filter universal variables on larger levels
        let universal_assignment: FxHashMap<Variable, bool> = global
            .assignments
            .iter()
            .filter_map(|(&var, &val)| {
                if matrix.prefix.variables().get(var).is_universal()
                    && !matrix
                        .prefix
                        .get_scope(abstraction.scope_id.unwrap())
                        .dependencies
                        .contains(&var)
                {
                    Some((var, val))
                } else {
                    None
                }
            })
            .collect();
        if !universal_assignment.is_empty() {
            #[cfg(feature = "statistics")]
            global
                .statistics
                .inc(GlobalSolverEvents::ExpansionRefinements);
            abstraction.expansion_refinement(matrix, &universal_assignment, &global.level_lookup);
        }
    }

    #[cfg(feature = "statistics")]
    pub(crate) fn print_statistics(&self) {
        #[cfg(feature = "statistics")]

        println!("{}", self.global.statistics);
        self.global.timings.print();
        println!();

        for level in &self.levels {
            match level {
                SolverLevel::Existential(abstractions) => {
                    for abstraction in abstractions {
                        abstraction.print_statistics();
                    }
                }
                SolverLevel::Universal(abstraction) => {
                    abstraction.print_statistics();
                }
            }
        }
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
enum SolveLevelResult {
    ContinueInner,
    /// A conflict for the existential player, with level to refine
    UnsatConflict(Option<usize>),
    /// A conflict for the universal player, with originating level
    SatConflict(usize),
}

impl<'a> super::Solver for DCaqeSolver<'a> {
    fn solve(&mut self) -> SolverResult {
        trace!("solve");

        let mut level = 0;
        loop {
            let result = self.solve_level(level);
            level = match self.process_level_result(level, result) {
                Ok(l) => l,
                Err(res) => return res,
            }
        }
    }
}

enum SolverLevel {
    Universal(Box<Abstraction>),
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
            Self::Universal(abstraction) => abstraction.add_clauses(matrix, level_lookup, clauses),
            Self::Existential(abstractions) => {
                for abstraction in abstractions.iter_mut() {
                    abstraction.add_clauses(matrix, level_lookup, clauses)
                }
            }
        }
    }
}

#[cfg(feature = "statistics")]
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Debug)]
enum GlobalSolverEvents {
    ConflictClauses,
    DependencyConflicts,
    ExpansionRefinements,
    ProcessLevelResult,
}

#[cfg(feature = "statistics")]
impl std::fmt::Display for GlobalSolverEvents {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            GlobalSolverEvents::ConflictClauses => write!(f, "ConflictClauses     "),
            GlobalSolverEvents::DependencyConflicts => write!(f, "DependencyConflicts "),
            GlobalSolverEvents::ExpansionRefinements => write!(f, "ExpansionRefinements"),
            GlobalSolverEvents::ProcessLevelResult => write!(f, "ProcessLevelResult  "),
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

    config: DCaqeSpecificSolverConfig,

    #[cfg(feature = "statistics")]
    statistics: CountingStats<GlobalSolverEvents>,

    #[cfg(feature = "statistics")]
    timings: TimingStats<GlobalSolverEvents>,
}

impl GlobalSolverData {
    fn new(matrix: &DQMatrix, config: &DCaqeSpecificSolverConfig) -> Self {
        Self {
            assignments: FxHashMap::default(),
            level_lookup: FxHashMap::default(),
            unsat_core: BitVec::from_elem(matrix.clauses.len(), false),
            config: config.clone(),
            #[cfg(feature = "statistics")]
            statistics: CountingStats::new(),
            #[cfg(feature = "statistics")]
            timings: TimingStats::new(),
        }
    }

    /// Returns the level to continue with refining the unsat result
    fn get_unsat_level(&self, matrix: &DQMatrix, orig_level: usize) -> Option<usize> {
        self.unsat_core
            .iter()
            .enumerate()
            .filter(|(_, val)| *val)
            .fold(None, |val, (clause_id, _)| {
                let clause = &matrix.clauses[clause_id];
                clause
                    .iter()
                    .filter(|l| {
                        let info = matrix.prefix.variables().get(l.variable());
                        info.is_existential() && self.level_lookup[&l.variable()] < orig_level
                    })
                    .fold(val, |val, l| {
                        let level = self.level_lookup[&l.variable()];
                        match val {
                            Some(v) => Some(std::cmp::max(v, level)),
                            None => Some(level),
                        }
                    })
            })
    }

    fn build_conflict_clause(&mut self, matrix: &DQMatrix, level: usize) -> Clause {
        let mut literals = Vec::new();
        for (clause_id, _) in self.unsat_core.iter().enumerate().filter(|(_, val)| *val) {
            let clause = &matrix.clauses[clause_id];
            literals.extend(
                clause
                    .iter()
                    .filter(|l| self.level_lookup[&l.variable()] <= level),
            );
        }

        #[cfg(feature = "statistics")]
        self.statistics.inc(GlobalSolverEvents::ConflictClauses);

        Clause::new(literals)
    }

    #[allow(clippy::too_many_lines)]
    fn dependency_conflict_resolution(
        &mut self,
        matrix: &mut DQMatrix,
        conflict_clause: Clause,
        universally_reduced: bool,
    ) -> DepConfResResult {
        let mut maximal_scopes: MaxElements<Scope> = MaxElements::new();
        for &literal in conflict_clause.iter() {
            let info = matrix.prefix.variables().get(literal.variable());
            if let Some(scope_id) = *info.get_scope_id() {
                // TODO: we need a clone here, since the prefix is modified below, but this is wasteful
                let scope = matrix.prefix.get_scope(scope_id).clone();
                maximal_scopes.add(scope);
            }
        }
        debug_assert!(
            maximal_scopes.len() > 0,
            "empty clauses are handeled before"
        );
        if maximal_scopes.len() == 1 {
            if universally_reduced {
                // The Skolem function has changed due to universal reduction
                covered_by!("refinement_universal_reduction");
                return DepConfResResult::Split(vec![matrix.add(conflict_clause)], vec![]);
            } else {
                let scope = maximal_scopes.remove(0);
                return DepConfResResult::Refine(
                    matrix.prefix.scope_lookup(&scope.dependencies).unwrap(),
                );
            }
        }
        debug!("dependency conflict detected");

        #[cfg(feature = "statistics")]
        self.statistics.inc(GlobalSolverEvents::DependencyConflicts);

        let mut arbiters = Vec::new();
        let mut clauses = Vec::new();

        let mut remaining = conflict_clause;
        let mut meets: MaxElements<Scope> = MaxElements::new();

        while maximal_scopes.len() > 1 {
            // get maximal scope with only one interesction with other scope
            // if this is not possible, there is a dependency cycle

            let index = match maximal_scopes.get_first(|scope| {
                meets.clear();
                for other in maximal_scopes.iter() {
                    if scope == other {
                        continue;
                    }
                    let intersection = scope
                        .dependencies
                        .intersection(&other.dependencies)
                        .cloned()
                        .collect();
                    meets.add(Scope::new(&intersection));
                }
                meets.len() == 1
            }) {
                Some(i) => i,
                None => return DepConfResResult::Cycle,
            };
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
                    if let Some(scope_id) = *info.get_scope_id() {
                        let other = &matrix.prefix.scopes[scope_id as usize];
                        other.dependencies.is_subset(&scope.dependencies)
                            && !other.dependencies.is_subset(&meet.dependencies)
                    } else {
                        // universal variable
                        scope.dependencies.contains(&literal.variable())
                    }
                })
                .cloned()
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
                    if let Some(scope_id) = *info.get_scope_id() {
                        let other = &matrix.prefix.scopes[scope_id as usize];
                        !other.dependencies.is_subset(&scope.dependencies)
                            || other.dependencies.is_subset(&meet.dependencies)
                    } else {
                        // universal variable not in difference of maximal element and meet
                        meet.dependencies.contains(&literal.variable())
                            || !scope.dependencies.contains(&literal.variable())
                    }
                })
                .cloned()
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

        DepConfResResult::Split(clauses, arbiters)
    }
}

/// Result of the dependency conflict resolution
enum DepConfResResult {
    Split(Vec<ClauseId>, Vec<Variable>),
    Refine(ScopeId),
    Cycle,
}

#[cfg(feature = "statistics")]
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
enum SolverScopeEvents {
    SolveScopeAbstraction,
    Refinement,
}

#[cfg(feature = "statistics")]
impl std::fmt::Display for SolverScopeEvents {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            SolverScopeEvents::SolveScopeAbstraction => write!(f, "SolveScopeAbstraction"),
            SolverScopeEvents::Refinement => write!(f, "Refinement"),
        }
    }
}

#[allow(clippy::enum_variant_names)]
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

    /// learns Skolem functions during solving
    learner: Option<SkolemFunctionLearner>,

    /// store partially expanded variables
    /// maps a variable and a cube representing the assignment of its dependencies to a SAT solver literal
    expanded: FxHashMap<(Variable, Vec<Literal>), Lit>,

    #[cfg(feature = "statistics")]
    statistics: TimingStats<SolverScopeEvents>,
}

impl Abstraction {
    fn new(
        matrix: &DQMatrix,
        level: usize,
        scope_id: Option<ScopeId>,
        needs_learner: bool,
    ) -> Self {
        let mut sat = cryptominisat::Solver::new();
        sat.set_num_threads(1);
        let is_max_level = scope_id.map_or(false, |scope_id| {
            let scope = &matrix.prefix.scopes[scope_id];
            matrix.prefix.is_maximal(scope)
        });
        let learner = if needs_learner {
            Some(SkolemFunctionLearner::new())
        } else {
            None
        };
        Self {
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
            learner,
            expanded: FxHashMap::default(),
            #[cfg(feature = "statistics")]
            statistics: TimingStats::new(),
        }
    }

    fn new_universal(
        matrix: &DQMatrix,
        variables: &FxHashSet<Variable>,
        level_lookup: &FxHashMap<Variable, usize>,
        level: usize,
    ) -> Self {
        // build SAT instance for negation of clauses, i.e., basically we only build binary clauses
        debug_assert!(!variables.is_empty());

        let mut abs = Self::new(matrix, level, None, false);

        // add variables of scope to sat solver
        for &variable in variables {
            abs.variable_to_sat.insert(variable, abs.sat.new_var());
        }

        for (clause_id, clause) in matrix.enumerate() {
            abs.encode_universal_clause(matrix, clause_id as ClauseId, clause, level_lookup);
        }

        abs.inc_sat_lit = Some(abs.sat.new_var());

        abs
    }

    fn encode_universal_clause(
        &mut self,
        _matrix: &DQMatrix,
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
        needs_learner: bool,
    ) -> Self {
        let mut abs = Self::new(matrix, level, Some(scope_id), needs_learner);
        let mut sat_clause = Vec::new();

        // add variables of scope to sat solver
        for &variable in &scope.existentials {
            abs.variable_to_sat.insert(variable, abs.sat.new_var());
        }

        for (clause_id, clause) in matrix.enumerate() {
            abs.encode_existential_clause(matrix, clause_id, clause, &mut sat_clause, scope);
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
                if let Some(scope_id) = *info.get_scope_id() {
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
        for &(clause_id, mut t_literal) in &self.t_literals {
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
        for (&variable, &sat_var) in &self.variable_to_sat {
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

    fn entry_minimization(&mut self, matrix: &DQMatrix, global: &mut GlobalSolverData) {
        trace!("entry_minimization");

        let scope = matrix
            .prefix
            .get_scope(self.scope_id.expect("only for existential abstractions"));

        // add clauses to entry where the current scope is maximal
        global.unsat_core.union(&self.max_clauses);

        for variable in &scope.existentials {
            let value = global.assignments[variable];
            let literal = Literal::new(*variable, !value);

            // check if assignment satisfied clause in unsat core
            // if yes, it can be removed
            let mut needed = false;
            for &clause_id in matrix.occurrences(literal) {
                if global.unsat_core[clause_id as usize] {
                    needed = true;
                    global.unsat_core.set(clause_id as usize, false);
                }
            }

            // greedy flipping is unsound if values are fixed by skolem function
            if let Some(ref learner) = self.learner {
                if learner.last_matched {
                    continue;
                }
            }

            if !needed {
                debug!("flip {} -> {}", literal.dimacs(), (-literal).dimacs());
                // the current value set is not needed for the entry, try other polarity
                for &clause_id in matrix.occurrences(-literal) {
                    if global.unsat_core[clause_id as usize] {
                        global.unsat_core.set(clause_id as usize, false);
                    }
                    global
                        .assignments
                        .insert(literal.variable(), literal.signed());
                }
            }
        }

        if let Some(ref mut learner) = self.learner {
            learner.learn(matrix, global, scope);
        }
    }

    fn add_b_lit_and_adapt_abstraction(
        clause_id: ClauseId,
        sat: &mut cryptominisat::Solver,
        b_literals: &[(ClauseId, Lit)],
        t_literals: &mut Vec<(ClauseId, Lit)>,
        reverse_t_literals: &mut FxHashMap<u32, ClauseId>,
    ) -> Lit {
        // first check if there is a b-literal for clause
        // if yes, just return it (the currents scope influences clause since there is at least one variable contained)
        // if no, we continue
        if let Ok(pos) = b_literals.binary_search_by(|elem| elem.0.cmp(&clause_id)) {
            return b_literals[pos].1;
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

        #[cfg(feature = "statistics")]
        let mut _timer = self.statistics.start(SolverScopeEvents::Refinement);

        let blocking_clause = &mut self.sat_solver_assumptions;
        blocking_clause.clear();

        #[cfg(debug_assertions)]
        let mut debug_print = String::new();

        for (clause_id, _) in learned.iter().enumerate().filter(|(_, val)| *val) {
            #[allow(clippy::cast_possible_truncation)]
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

    fn expansion_refinement(
        &mut self,
        matrix: &DQMatrix,
        assignment: &FxHashMap<Variable, bool>,
        _level_lookup: &FxHashMap<Variable, usize>,
    ) {
        trace!("expansion refinement");
        debug_assert!(!assignment.is_empty());
        debug_assert!(!self.is_universal());

        //dbg!(self.level);
        //dbg!(assignment);

        #[cfg(debug_assertions)]
        {
            // check that assignment is universal
            for &var in assignment.keys() {
                assert!(matrix.prefix.variables().get(var).is_universal());
            }
        }

        let blocking_clause = &mut self.sat_solver_assumptions;
        let sat = &mut self.sat;

        for (clause_id, clause) in matrix.enumerate() {
            // check if the universal assignment satisfies the clause
            if clause.is_satisfied_by_assignment(assignment) {
                continue;
            }

            blocking_clause.clear();

            let mut outer_variables = false;

            // add the clause to the abstraction
            // variables bound by inner existential quantifier have to be renamed
            for &literal in clause.iter() {
                let info = matrix.prefix.variables().get(literal.variable());
                /*let lvl = level_lookup[&literal.variable()];
                if lvl <= self.level {
                    if lvl < self.level || *info.get_scope_id() != self.scope_id {
                        outer_variables = true
                    }
                    // ignore variables
                    continue;
                }
                if info.is_universal() {
                    // inner universal variables are eliminated
                    continue;
                }*/
                let scope = matrix.prefix.get_scope(self.scope_id.unwrap());
                if let Some(scope_id) = *info.get_scope_id() {
                    // existential variable
                    if scope_id == self.scope_id.unwrap() {
                        continue;
                    }
                    let other_scope = matrix.prefix.get_scope(scope_id);
                    if other_scope.dependencies.is_subset(&scope.dependencies) {
                        outer_variables = true;
                    } else {
                        // continue with encoding
                    }
                } else {
                    // universal variable
                    if scope.dependencies.contains(&literal.variable()) {
                        outer_variables = true;
                        debug_assert!(!assignment.contains_key(&literal.variable()));
                    } else {
                        debug_assert!(assignment.contains_key(&literal.variable()));
                    }
                    continue;
                }
                debug_assert!(info.is_existential());
                let mut deps: Vec<Literal> = assignment
                    .iter()
                    .filter_map(|(&var, val)| {
                        if info.dependencies().contains(&var) {
                            Some(Literal::new(var, !val))
                        } else {
                            None
                        }
                    })
                    .collect();
                deps.sort(); // make it unique
                let entry = self
                    .expanded
                    .entry((literal.variable(), deps))
                    .or_insert_with(|| sat.new_var());
                let mut sat_var = *entry;
                if literal.signed() {
                    sat_var = !sat_var;
                }
                blocking_clause.push(sat_var);
                //eprint!("{} ", literal.dimacs());
            }
            if blocking_clause.is_empty() {
                continue;
            }

            if self
                .b_literals
                .binary_search_by(|elem| elem.0.cmp(&clause_id))
                .is_ok()
                || outer_variables
            {
                let sat_lit = Self::add_b_lit_and_adapt_abstraction(
                    clause_id,
                    sat,
                    &self.b_literals,
                    &mut self.t_literals,
                    &mut self.reverse_t_literals,
                );
                blocking_clause.push(sat_lit);
                //eprint!("b-lit");
            }
            //eprintln!("");
            sat.add_clause(&blocking_clause);
        }
    }

    /// Resets the abstraction completely, i.e., removes all learnt clauses.
    /// Only applicable for universal levels.
    fn reset(&mut self) {
        debug_assert!(self.is_universal());
        if let Some(inc_lit) = self.inc_sat_lit {
            self.sat.add_clause(&[inc_lit]);
        }
        self.inc_sat_lit = Some(self.sat.new_var());
    }

    fn solve(&mut self, matrix: &DQMatrix, global: &mut GlobalSolverData) -> AbstractionResult {
        trace!("solve");

        #[cfg(feature = "statistics")]
        let mut _timer = self
            .statistics
            .start(SolverScopeEvents::SolveScopeAbstraction);

        debug!("");
        info!("solve level {}", self.level);
        if let Some(scope_id) = self.scope_id {
            let scope = matrix.prefix.get_scope(scope_id);
            debug!("{:?}", scope);

            if let Some(ref mut learner) = self.learner {
                if learner.matches(matrix, global, scope) {
                    covered_by!("skolem_function_matched");
                    return AbstractionResult::CandidateFound;
                }
            }
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

    #[cfg(feature = "statistics")]
    pub fn print_statistics(&self) {
        println!("scope {:?} at level {}", self.scope_id, self.level);
        self.statistics.print();
    }
}

#[derive(Debug)]
pub(crate) struct MaxElements<T>
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
    pub(crate) fn new() -> Self {
        Self {
            elements: Vec::new(),
        }
    }

    /// We remove all elements that are smaller than `element`.
    /// Then, we add `element` if there is no other element that is greater or equal.
    pub(crate) fn add(&mut self, element: T) {
        self.elements.retain(|other|
            // !(other < &element)
            match other.partial_cmp(&element) {
                Some(Ordering::Less) => false,
                _ => true,
            });
        let subsumed = self.elements.iter().any(|other| other >= &element);
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
            .find_map(|(i, ele)| if f(ele) { Some(i) } else { None })
    }

    fn remove(&mut self, index: usize) -> T {
        self.elements.remove(index)
    }

    pub(crate) fn len(&self) -> usize {
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

struct SkolemFunctionLearner {
    sat: cryptominisat::Solver,
    incremental: Lit,
    variable2sat: FxHashMap<Variable, Lit>,
    assumptions: Vec<Lit>,
    /// remembers the result of the last call to `matches`
    last_matched: bool,
}

/// Implements the part of learning the Skolem function during solving
impl SkolemFunctionLearner {
    fn new() -> Self {
        let mut sat = cryptominisat::Solver::new();
        let incremental = sat.new_var();
        sat.add_clause(&[incremental]);
        Self {
            sat,
            incremental,
            variable2sat: FxHashMap::default(),
            assumptions: Vec::new(),
            last_matched: false,
        }
    }

    fn reset(&mut self) {
        trace!("SkolemFunctionLearner::reset");
        self.sat = cryptominisat::Solver::new();
        self.incremental = self.sat.new_var();
        self.sat.add_clause(&[self.incremental]);
        self.variable2sat.clear();
    }

    /// Learns the function case of the Skolem function represented by the entry in
    /// `global.unsat_core` for the variables bound by `scope`.
    fn learn(&mut self, matrix: &DQMatrix, global: &GlobalSolverData, scope: &Scope) {
        trace!("SkolemFunctionLearner::learn");
        // encodes query
        // prevIncLit => ite(entry, assignment, newLit)

        let mut conjunctive_lits = Vec::new();
        let sat_clause = &mut self.assumptions;
        sat_clause.clear();
        let sat = &mut self.sat;

        // builds the conjunction of entries
        for (clause_id, _) in global.unsat_core.iter().enumerate().filter(|(_, val)| *val) {
            let clause = &matrix.clauses[clause_id];

            debug_assert!(sat_clause.is_empty());

            let mut satisfied = false;
            for &literal in clause.iter().filter(|l| {
                !scope.existentials.contains(&l.variable())
                    && matrix.prefix.depends_on_scope(scope, l.variable())
            }) {
                let value = global.assignments[&literal.variable()];
                let assigned_lit = Literal::new(literal.variable(), !value);
                if literal == assigned_lit {
                    satisfied = true;
                }
                let sat_lit = *self
                    .variable2sat
                    .entry(literal.variable())
                    .or_insert_with(|| sat.new_var());
                if literal.signed() {
                    sat_clause.push(!sat_lit);
                } else {
                    sat_clause.push(sat_lit);
                }
            }

            if !satisfied {
                // entry not relevant for current scope
                sat_clause.clear();
                continue;
            }

            let conjunction = sat.new_var();
            sat_clause.push(!conjunction);
            sat.add_clause(sat_clause);
            sat_clause.clear();
            conjunctive_lits.push(conjunction);
        }

        debug_assert!(sat_clause.is_empty());
        let precondition = sat.new_var(); // 1 iff entry holds
        sat_clause.push(precondition);
        for &conjunction in &conjunctive_lits {
            sat_clause.push(!conjunction);
            sat.add_clause(&[!precondition, conjunction]);
        }
        sat.add_clause(&sat_clause);
        sat_clause.clear();

        debug_assert!(sat_clause.is_empty());
        let assignment_lit = sat.new_var(); // 1 iff assignment holds
        sat_clause.push(assignment_lit);
        for &variable in &scope.existentials {
            let sat_lit = *self
                .variable2sat
                .entry(variable)
                .or_insert_with(|| sat.new_var());
            if global.assignments[&variable] {
                sat_clause.push(!sat_lit);
                sat.add_clause(&[!assignment_lit, sat_lit]);
            } else {
                sat_clause.push(sat_lit);
                sat.add_clause(&[!assignment_lit, !sat_lit]);
            }
        }
        sat.add_clause(&sat_clause);
        sat_clause.clear();

        let previous_inc_lit = self.incremental;
        self.incremental = sat.new_var();

        // if then else
        // not prev || not prec || assig == (prev && prec) -> assig
        sat.add_clause(&[!previous_inc_lit, !precondition, assignment_lit]);
        sat.add_clause(&[!previous_inc_lit, precondition, self.incremental]);
    }

    /// Checks if the current assignment in `global->assignment` matches the previous
    /// learned Skolem function.
    /// If yes, the assignment is updated accordingly.
    fn matches(
        &mut self,
        _matrix: &DQMatrix,
        global: &mut GlobalSolverData,
        scope: &Scope,
    ) -> bool {
        trace!("SkolemFunctionLearner::match");
        self.assumptions.clear();

        // assume incremental literal negatively
        self.assumptions.push(!self.incremental);

        // assume dependent variables
        for (variable, &sat_lit) in &self.variable2sat {
            if scope.existentials.contains(variable) {
                continue;
            }
            if global.assignments[variable] {
                self.assumptions.push(sat_lit);
            } else {
                self.assumptions.push(!sat_lit);
            }
        }

        let res = match self.sat.solve_with_assumptions(&self.assumptions) {
            Lbool::True => {
                // found a match, update assignments

                #[cfg(debug_assertions)]
                let mut debug_print = String::new();

                let model = self.sat.get_model();
                for variable in &scope.existentials {
                    let sat_var = self.variable2sat[variable];
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

                    let old = global.assignments.entry(*variable).or_insert(value);
                    *old = value;
                }
                debug!("replay Skolem function");
                #[cfg(debug_assertions)]
                debug!("assignment {}", debug_print);

                true
            }
            Lbool::False => false,
            _ => unreachable!(),
        };

        self.last_matched = res;
        res
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::parse::dqdimacs;
    use crate::solve::Solver;

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
        let config = DCaqeSpecificSolverConfig::default();
        let mut solver = DCaqeSolver::new(&mut matrix, &config);
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
        let config = DCaqeSpecificSolverConfig::default();
        let mut solver = DCaqeSolver::new(&mut matrix, &config);
        assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
    }

    #[test]
    fn test_unsat_universal_reduction() {
        covers!("unsat_universal_reduction");
        let instance = "c
p cnf 7 4
a 1 2 3 4 0
d 5 2 3 0
d 6 3 1 4 0
d 7 2 3 4 0
-2 -4 6 -7 0
2 -6 -7 0
2 -5 0
7 0
";
        let mut matrix = dqdimacs::parse(&instance).unwrap();
        let config = DCaqeSpecificSolverConfig::default();
        let mut solver = DCaqeSolver::new(&mut matrix, &config);
        assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
    }

    #[test]
    fn test_refinement_universal_reduction() {
        covers!("refinement_universal_reduction");
        let instance = "c
p cnf 13 9
a 5 4 0
d 7 4 0
d 9 5 0
d 13 5 4 0
d 6 5 0
d 8 5 0
-5 13 0
4 5 -13 0
9 13 0
-4 13 0
-9 -13 0
-6 9 0
6 13 0
-8 -9 0
8 -13 0
";
        let mut matrix = dqdimacs::parse(&instance).unwrap();
        let config = DCaqeSpecificSolverConfig::default();
        let mut solver = DCaqeSolver::new(&mut matrix, &config);
        assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
    }

    #[test]
    fn test_unsat_fix_skolem() {
        covers!("skolem_function_matched");
        let instance = "c
p cnf 8 6
a 1 2 3 0
d 4 1 0
d 5 2 0
d 6 1 3 0
d 7 1 2 3 0
d 8 1 2 3 0
-2 5 0
-2 7 0
-7 -6 0
3 6 -8 -4 0
2 8 0
-5 4 0
";
        let mut matrix = dqdimacs::parse(&instance).unwrap();
        let config = DCaqeSpecificSolverConfig::default();
        let mut solver = DCaqeSolver::new(&mut matrix, &config);
        assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
    }

    #[test]
    fn test_expansion_regression() {
        let instance = "c
p cnf 7 3
a 1 2 3 4 0
d 5 0
d 6 1 3 0
d 7 1 2 4 0
6 7 0
-7 0
5 -6 0
";
        let mut matrix = dqdimacs::parse(&instance).unwrap();
        let config = DCaqeSpecificSolverConfig::default();
        let mut solver = DCaqeSolver::new(&mut matrix, &config);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
    }

    #[test]
    fn test_expansion_regression2() {
        let instance = "c
p cnf 9 3
a 1 2 3 4 5 0
d 6 1 2 0
d 7 4 5 0
d 8 2 3 0
d 9 5 0
-7 0
6 8 0
7 9 0
";
        let mut matrix = dqdimacs::parse(&instance).unwrap();
        let config = DCaqeSpecificSolverConfig::default();
        let mut solver = DCaqeSolver::new(&mut matrix, &config);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
    }
}
