use super::super::matrix::hierarchical::*;
use super::super::parse::qdimacs;
use super::super::*;
use bit_vec::BitVec;
use cryptominisat::*;
use log::{debug, info, trace};
use rustc_hash::FxHashMap;
use std::collections::BTreeMap;

#[cfg(feature = "statistics")]
use crate::utils::statistics::TimingStats;

type QMatrix = Matrix<HierarchicalPrefix>;

#[derive(Debug, Clone, Copy)]
pub struct CaqeSolverOptions {
    pub strong_unsat_refinement: bool,
    pub expansion_refinement: bool,
    pub refinement_literal_subsumption: bool,
    pub abstraction_literal_optimization: bool,
    pub miniscoping: bool,
    pub dependency_schemes: bool,
    pub build_conflict_clauses: bool,
    pub conflict_clause_expansion: bool,
}

pub struct CaqeSolver<'a> {
    matrix: &'a mut QMatrix,
    result: SolverResult,
    global: GlobalSolverData,
    abstraction: Vec<Box<ScopeRecursiveSolver>>,
}

struct ScopeRecursiveSolver {
    data: ScopeSolverData,
    next: Vec<Box<ScopeRecursiveSolver>>,
}

struct GlobalSolverData {
    options: CaqeSolverOptions,
    conflicts: Vec<(BitVec, u32)>,
}

/// Contains the SAT solver and the translation between Variables and SAT solver literals
struct SatAndTranslation {
    sat: cryptominisat::Solver,
    variable_to_sat: FxHashMap<Variable, Lit>,
    t_literals: BTreeMap<ClauseId, Lit>,
    b_literals: BTreeMap<ClauseId, Lit>,

    /// lookup from sat solver variables to clause id's
    reverse_t_literals: FxHashMap<u32, ClauseId>,
}

struct ScopeSolverData {
    sat: SatAndTranslation,

    variables: Vec<Variable>,

    assignments: FxHashMap<Variable, bool>,

    /// stores for every clause whether the clause is satisfied or not by assignments to outer variables
    entry: BitVec,

    /// Stores the clauses for which the current level is maximal, i.e.,
    /// there is no literal of an inner scope contained.
    /// For universal scopes, it stores the clauses which are only influenced by
    /// the current, or some inner, scope.
    max_clauses: BitVec,

    /// Stores the clauses which are relevant, i.e., belong to the current branch in quantifier prefix tree
    relevant_clauses: BitVec,

    /// stores the assumptions given to sat solver
    sat_solver_assumptions: Vec<Lit>,

    is_universal: bool,
    scope_id: ScopeId,
    level: u32,

    /// stores for clause-ids whether there is a strong-unsat optimized lit
    strong_unsat_cache: FxHashMap<ClauseId, (Lit, bool)>,
    conjunction: Vec<ClauseId>,

    /// store partially expanded variables
    /// maps a variable and a cube representing the assignment of its dependencies to a SAT solver literal
    expanded: FxHashMap<(Variable, Vec<Literal>), Lit>,
    expansions: Vec<FxHashMap<Variable, bool>>,
    /// stores the index of the conflict (global vec `conflicts`) that is next to be used in expansion refinement
    next_conflict: usize,

    /// stores the result of recursive calls to branches
    sub_result: SolverResult,

    #[cfg(feature = "statistics")]
    statistics: TimingStats<SolverScopeEvents>,
}

impl<'a> CaqeSolver<'a> {
    pub fn new(matrix: &mut QMatrix) -> CaqeSolver {
        Self::new_with_options(matrix, CaqeSolverOptions::default())
    }

    pub fn new_with_options(matrix: &mut QMatrix, options: CaqeSolverOptions) -> CaqeSolver {
        let mut abstractions = Vec::new();
        for scope_id in matrix.prefix.roots.iter() {
            abstractions.push(ScopeRecursiveSolver::init_abstraction_recursively(
                matrix, &options, *scope_id,
            ));
        }
        debug_assert!(!matrix.conflict());
        CaqeSolver {
            matrix: matrix,
            result: SolverResult::Unknown,
            global: GlobalSolverData::new(options),
            abstraction: abstractions,
        }
    }

    #[cfg(feature = "statistics")]
    pub(crate) fn print_statistics(&self, statistics: Statistics) {
        let mut iterations = 0;

        fn get_iterations_rec(scope: &ScopeRecursiveSolver) -> usize {
            let num = scope
                .data
                .statistics
                .count(SolverScopeEvents::SolveScopeAbstraction);
            num + scope
                .next
                .iter()
                .fold(0, |val, next| val + get_iterations_rec(next))
        }

        for abstraction in self.abstraction.iter() {
            iterations += get_iterations_rec(abstraction);
        }
        println!("iterations: {}", iterations);

        if statistics == Statistics::Detailed {
            for abstraction in self.abstraction.iter() {
                abstraction.print_statistics();
            }
        }
    }

    pub fn qdimacs_output(&self) -> qdimacs::PartialQDIMACSCertificate {
        let mut certificate = qdimacs::PartialQDIMACSCertificate::new(
            self.result,
            self.matrix.prefix.variables().orig_max_variable_id(),
            self.matrix.orig_clause_num,
        );

        if self.result == SolverResult::Unknown {
            return certificate;
        }

        // get the first scope that contains variables (the scope 0 may be empty)
        let mut top_level = Vec::new();
        let all_outer_scopes_empty = self.matrix.prefix.roots.iter().all(|scope_id| {
            self.matrix.prefix.scopes[scope_id.to_usize()]
                .variables
                .is_empty()
        });
        let is_universal = if all_outer_scopes_empty {
            // top-level existential scope is empty
            for abstraction in self.abstraction.iter() {
                top_level.extend(&abstraction.next);
            }
            true
        } else {
            top_level.extend(&self.abstraction);
            false
        };

        // output the variable assignment if possible
        if self.result == SolverResult::Satisfiable && is_universal
            || self.result == SolverResult::Unsatisfiable && !is_universal
        {
            return certificate;
        }

        // go thorough all scopes in the level
        // for existential level: combine the assignments
        // for universal level: select only one level
        for scope in top_level.iter() {
            if self.result == SolverResult::Unsatisfiable
                && scope.data.sub_result != SolverResult::Unsatisfiable
            {
                continue;
            }

            for variable in scope.data.variables.iter() {
                let value = scope.data.assignments[variable];
                let info = &self.matrix.prefix.variables().get(*variable);
                let orig_variable = if info.copy_of != 0u32.into() {
                    info.copy_of
                } else {
                    *variable
                };
                certificate.add_assignment(Literal::new(orig_variable, !value));
            }

            if self.result == SolverResult::Unsatisfiable {
                // only one assignment for universal quantifier
                break;
            }
        }

        certificate
    }
}

impl<'a> super::Solver for CaqeSolver<'a> {
    fn solve(&mut self) -> SolverResult {
        for abstraction in self.abstraction.iter_mut() {
            self.global.conflicts.clear();
            let result = abstraction.solve_recursive(self.matrix, &mut self.global);
            if result == SolverResult::Unsatisfiable {
                self.result = SolverResult::Unsatisfiable;
                return result;
            }
        }
        self.result = SolverResult::Satisfiable;
        self.result
    }
}

impl Default for CaqeSolverOptions {
    fn default() -> CaqeSolverOptions {
        CaqeSolverOptions {
            strong_unsat_refinement: false,
            expansion_refinement: true,
            refinement_literal_subsumption: false,
            abstraction_literal_optimization: true,
            miniscoping: true,
            dependency_schemes: true,
            build_conflict_clauses: true,
            conflict_clause_expansion: false,
        }
    }
}

impl GlobalSolverData {
    fn new(options: CaqeSolverOptions) -> GlobalSolverData {
        GlobalSolverData {
            options,
            conflicts: Vec::new(),
        }
    }
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
        match *self {
            SolverScopeEvents::SolveScopeAbstraction => write!(f, "SolveScopeAbstraction"),
            SolverScopeEvents::Refinement => write!(f, "Refinement"),
        }
    }
}

impl ScopeRecursiveSolver {
    fn new(
        matrix: &QMatrix,
        options: &CaqeSolverOptions,
        scope: &Scope,
        next: Vec<Box<ScopeRecursiveSolver>>,
    ) -> ScopeRecursiveSolver {
        let mut relevant_clauses = BitVec::from_elem(matrix.clauses.len(), false);
        for next_scope in next.iter() {
            #[cfg(debug_assertions)]
            {
                // the branches have pairwise disjoint relevant clauses
                let mut copy = relevant_clauses.clone();
                copy.intersect(&next_scope.data.relevant_clauses);
                assert!(copy.none());
            }
            relevant_clauses.union(&next_scope.data.relevant_clauses);
        }
        let mut candidate = ScopeRecursiveSolver {
            data: ScopeSolverData::new(matrix, scope, relevant_clauses),
            next: next,
        };

        // add variables of scope to sat solver
        for &variable in scope.variables.iter() {
            candidate
                .data
                .sat
                .variable_to_sat
                .insert(variable, candidate.data.sat.sat.new_var());
        }

        match scope.quant {
            Quantifier::Existential => candidate.data.new_existential(matrix, options, scope),
            Quantifier::Universal => candidate.data.new_universal(matrix, options, scope),
        }

        candidate
    }

    fn init_abstraction_recursively(
        matrix: &QMatrix,
        options: &CaqeSolverOptions,
        scope_id: ScopeId,
    ) -> Box<ScopeRecursiveSolver> {
        let mut prev = Vec::new();
        for child_scope_id in matrix.prefix.next_scopes[scope_id.to_usize()].iter() {
            prev.push(Self::init_abstraction_recursively(
                matrix,
                options,
                *child_scope_id,
            ))
        }
        let scope = &matrix.prefix.scopes[scope_id.to_usize()];
        let result = Box::new(ScopeRecursiveSolver::new(matrix, options, scope, prev));

        #[cfg(debug_assertions)]
        {
            // check consistency of interface literals
            // for every b_lit in abstraction, there is a corresponding t_lit in one of its inner abstractions
            /*for &(clause_id, _b_lit) in result.data.b_literals.iter() {
                let mut current = &result;
                let mut found = false;
                while let Some(next) = current.next.as_ref() {
                    if next.data
                        .t_literals
                        .binary_search_by(|elem| elem.0.cmp(&clause_id))
                        .is_ok()
                    {
                        found = true;
                        break;
                    }
                    current = &next;
                }
                if !found {
                    panic!(
                        "missing t-literal for b-literal {} at scope {}",
                        clause_id, scope.id
                    );
                }
            }*/

            /*if scope_id == 0 {
                let mut abstractions = Vec::new();
                Self::verify_t_literals(&mut abstractions, result.as_ref());
            }*/
        }

        result
    }

    /*#[cfg(debug_assertions)]
    fn verify_t_literals<'a>(
        abstractions: &mut Vec<&'a ScopeRecursiveSolver>,
        scope: &'a ScopeRecursiveSolver,
    ) {
        // check that for every clause containing a t-literal at this scope,
        // there is a clause containing a b-literal in the previous scope
        abstractions.push(scope);
        for next in scope.next {
            for &(clause_id, _t_lit) in next.data.t_literals.iter() {
                let has_matching_b_lit = abstractions.iter().fold(false, |val, &abstraction| {
                    val
                        || abstraction
                            .data
                            .b_literals
                            .binary_search_by(|elem| elem.0.cmp(&clause_id))
                            .is_ok()
                });
                if !has_matching_b_lit {
                    panic!(
                        "missing b-literal for t-literal {} at scope {}",
                        clause_id, next.data.scope_id
                    );
                }
            }

            Self::verify_t_literals(abstractions, next.as_ref());
        }
        abstractions.pop();
    }*/

    fn solve_recursive(
        &mut self,
        matrix: &mut QMatrix,
        global: &mut GlobalSolverData,
    ) -> SolverResult {
        trace!("solve_recursive");

        // mutable split
        let current = &mut self.data;
        let next = &mut self.next;

        let good_result = if current.is_universal {
            SolverResult::Unsatisfiable
        } else {
            SolverResult::Satisfiable
        };
        let bad_result = if current.is_universal {
            SolverResult::Satisfiable
        } else {
            SolverResult::Unsatisfiable
        };
        debug_assert!(good_result != bad_result);

        loop {
            debug!("");
            info!(
                "solve scope {} at level {}",
                current.scope_id, current.level
            );

            #[cfg(feature = "statistics")]
            let mut timer = current
                .statistics
                .start(SolverScopeEvents::SolveScopeAbstraction);

            match current.check_candidate_exists(next) {
                Lbool::True => {
                    // there is a candidate solution, verify it recursively
                    current.update_assignment();

                    if next.is_empty() {
                        // innermost scope, propagate result to outer scopes
                        debug_assert!(!current.is_universal);
                        //current.entry.clear();
                        current.entry_minimization(matrix);
                        return good_result;
                    }

                    current.get_assumptions(matrix, next);

                    #[cfg(feature = "statistics")]
                    timer.stop();

                    current.sub_result = good_result;
                    for scope in next.iter_mut() {
                        let result = scope.solve_recursive(matrix, global);
                        if result == bad_result {
                            debug_assert!(result == bad_result);
                            current.sub_result = bad_result;

                            #[cfg(feature = "statistics")]
                            let mut _timer =
                                current.statistics.start(SolverScopeEvents::Refinement);

                            if !current.is_influenced_by_witness(matrix, scope) {
                                // copy witness
                                current.entry.clear();
                                current.entry.union(&scope.data.entry);
                                return bad_result;
                            }
                            current.refine(matrix, scope, global);
                            if global.options.build_conflict_clauses {
                                current.extract_conflict_clause(matrix, scope);
                            }
                        }
                    }

                    if current.sub_result == bad_result {
                        continue;
                    } else {
                        // copy entries from inner quantifier
                        current.entry.clear();
                        for scope in next.iter() {
                            current.entry.union(&scope.data.entry);
                        }
                        // apply entry optimization
                        if current.is_universal {
                            current.unsat_propagation();
                        } else {
                            current.entry_minimization(matrix);
                        }
                        return good_result;
                    }
                }
                Lbool::False => {
                    // there is no candidate solution, return witness
                    current.get_unsat_core();
                    return bad_result;
                }
                _ => panic!("inconsistent internal state"),
            }
        }
    }

    #[cfg(feature = "statistics")]
    pub fn print_statistics(&self) {
        println!("scope id {}, level {}", self.data.scope_id, self.data.level);
        self.data.statistics.print();
        for next in self.next.iter() {
            next.print_statistics()
        }
    }

    fn split(&mut self) -> (&mut ScopeSolverData, &mut Vec<Box<ScopeRecursiveSolver>>) {
        (&mut self.data, &mut self.next)
    }

    fn get_universal_assignmemnt(
        &self,
        mut assignment: FxHashMap<Variable, bool>,
    ) -> FxHashMap<Variable, bool> {
        if self.data.is_universal {
            assignment.extend(self.data.assignments.iter());
        }
        for next in self.next.iter() {
            assignment = next.get_universal_assignmemnt(assignment);
        }
        assignment
    }
}

impl SatAndTranslation {
    fn new(matrix: &QMatrix) -> Self {
        let mut sat = cryptominisat::Solver::new();
        sat.set_num_threads(1);
        SatAndTranslation {
            sat,
            variable_to_sat: FxHashMap::default(),
            t_literals: BTreeMap::new(),
            b_literals: BTreeMap::new(),
            reverse_t_literals: FxHashMap::default(),
        }
    }

    fn new_var(&mut self) -> Lit {
        self.sat.new_var()
    }

    fn lit_to_sat_lit(&self, literal: Literal) -> Lit {
        let lit = self.variable_to_sat[&literal.variable()];
        if literal.signed() {
            !lit
        } else {
            lit
        }
    }

    fn add_clause(&mut self, lits: &[Lit]) -> bool {
        self.sat.add_clause(lits)
    }

    fn solve_with_assumptions(&mut self, assumptions: &[Lit]) -> Lbool {
        self.sat.solve_with_assumptions(assumptions)
    }

    fn get_model(&self) -> &[Lbool] {
        self.sat.get_model()
    }

    fn get_conflict(&self) -> &[Lit] {
        self.sat.get_conflict()
    }

    fn add_b_lit_and_adapt_abstraction(&mut self, clause_id: ClauseId) -> Lit {
        // first check if there is a b-literal for clause
        // if yes, just return it (the currents scope influences clause since there is at least one variable contained)
        // if no, we continue
        if let Some(&b_lit) = self.b_literals.get(&clause_id) {
            return b_lit;
        };

        // we then check, if there is a corresponding t-literal
        // if yes, we return this instead
        // if no, we have to adapt the abstraction by inserting a new t-literal
        let reverse = &mut self.reverse_t_literals;
        let sat = &mut self.sat;
        let entry = self.t_literals.entry(clause_id).or_insert_with(|| {
            let var = sat.new_var();
            reverse.insert(var.var(), clause_id);
            var
        });

        // note that, we could also adapt b_literals (with the same sat_literal)
        // however, this is not necessary and not directly obvious
        // 1) reason *not* to do it: in get_assumptions we iterate over b_literals to check
        //    if we can improve the assumptions produced by the SAT solver. Since the clauses
        //    that are added here have no influence of current scope, this check is wasted time
        // 2) we do not *need* them, because abstraction entries are just copied from one
        //    scope to another

        *entry
    }
}

impl ScopeSolverData {
    fn new(matrix: &QMatrix, scope: &Scope, relevant_clauses: BitVec) -> ScopeSolverData {
        // assign all variables initially to zero, needed for expansion refinement
        let mut assignments = FxHashMap::default();
        for &variable in scope.variables.iter() {
            assignments.insert(variable, false);
        }
        ScopeSolverData {
            sat: SatAndTranslation::new(matrix),
            variables: scope.variables.clone(),
            assignments: assignments,
            entry: BitVec::from_elem(matrix.clauses.len(), false),
            max_clauses: BitVec::from_elem(matrix.clauses.len(), false),
            relevant_clauses: relevant_clauses,
            sat_solver_assumptions: Vec::new(),
            is_universal: scope.quant == Quantifier::Universal,
            scope_id: scope.id,
            level: scope.level,
            strong_unsat_cache: FxHashMap::default(),
            conjunction: Vec::new(),
            expanded: FxHashMap::default(),
            expansions: Vec::new(),
            next_conflict: 0,
            sub_result: SolverResult::Unknown,
            #[cfg(feature = "statistics")]
            statistics: TimingStats::new(),
        }
    }

    fn new_existential(&mut self, matrix: &QMatrix, options: &CaqeSolverOptions, scope: &Scope) {
        let sat_clause = &mut self.sat_solver_assumptions;
        sat_clause.clear();

        // build SAT instance for existential quantifier: abstract all literals that are not contained in quantifier into b- and t-literals
        'next_clause: for (clause_id, clause) in matrix.clauses.iter().enumerate() {
            debug_assert!(clause.len() != 0, "unit clauses indicate a problem");
            debug_assert!(sat_clause.is_empty());

            let mut contains_variables = false;
            let mut contains_outer_var = false;
            let mut contains_inner_var = false;
            let mut outer = None;
            let mut inner = None;
            let mut current = None;

            for &literal in clause.iter() {
                let info = matrix.prefix.variables().get(literal.variable());
                if info.scope_id.unwrap() == self.scope_id {
                    // variable of current scope
                    debug_assert!(self.sat.variable_to_sat.contains_key(&literal.variable()));
                    debug_assert!(info.level == self.level);
                    self.relevant_clauses.set(clause_id as usize, true);
                    current = Some(literal);
                    contains_variables = true;
                    sat_clause.push(self.sat.lit_to_sat_lit(literal));
                } else if info.level < scope.level {
                    outer = Some(literal);
                    contains_outer_var = true;
                } else if info.level > scope.level {
                    inner = Some(literal);
                    contains_inner_var = true;
                }
            }

            // add t- and b-lits to existential quantifiers:
            // * we add t-lit if there is an outer variable
            // * we add b-lit if there is an inner variable
            let need_t_lit = contains_variables && contains_outer_var;
            let need_b_lit = contains_variables && contains_inner_var;

            let mut outer_equal_to = None;
            let mut inner_equal_to = None;

            if !contains_outer_var && !contains_variables && contains_inner_var {
                // remove the clause from relevant clauses as current scope (nor any outer) influence it
                self.relevant_clauses.set(clause_id as usize, false);
            }

            if !contains_variables {
                debug_assert!(!need_t_lit);
                debug_assert!(!need_b_lit);
                debug_assert!(sat_clause.is_empty());
                continue;
            }
            // check if the clause is equal to another clause w.r.t. variables bound at the current level or outer
            // in this case, we do not need to add a clause to SAT solver, but rather just need an entry in b-literals
            if options.abstraction_literal_optimization && need_b_lit && current.is_some() {
                for &other_clause_id in matrix
                    .occurrences(current.unwrap())
                    .filter(|&&id| id < clause_id as ClauseId)
                {
                    let other_clause = &matrix.clauses[other_clause_id as usize];
                    if clause.is_equal_wrt_predicate(other_clause, |l| {
                        let info = matrix.prefix.variables().get(l.variable());
                        info.level <= scope.level
                    }) {
                        debug_assert!(need_b_lit);
                        if let Some(&b_lit) = self.sat.b_literals.get(&other_clause_id) {
                            self.sat.b_literals.insert(clause_id as ClauseId, b_lit);
                            sat_clause.clear();
                            continue 'next_clause;
                        }
                    }
                }
            }
            if false && options.abstraction_literal_optimization && outer.is_some() {
                for &other_clause_id in matrix
                    .occurrences(outer.unwrap())
                    .filter(|&&id| id < clause_id as ClauseId)
                {
                    let other_clause = &matrix.clauses[other_clause_id as usize];
                    if clause.is_equal_wrt_predicate(other_clause, |l| {
                        let info = matrix.prefix.variables().get(l.variable());
                        info.level < scope.level
                    }) {
                        debug_assert!(need_t_lit);
                        /*let pos = self
                            .sat
                            .t_literals
                            .binary_search_by(|elem| elem.0.cmp(&other_clause_id));
                        if pos.is_ok() {
                            let sat_var = self.sat.t_literals[pos.unwrap()].1;
                            outer_equal_to = Some(sat_var);
                            break;
                        }*/
                    }
                }
            }
            if false && options.abstraction_literal_optimization && inner.is_some() {
                for &other_clause_id in matrix
                    .occurrences(inner.unwrap())
                    .filter(|&&id| id < clause_id as ClauseId)
                {
                    let other_clause = &matrix.clauses[other_clause_id as usize];
                    if clause.is_equal_wrt_predicate(other_clause, |l| {
                        let info = matrix.prefix.variables().get(l.variable());
                        info.level > scope.level
                    }) {
                        debug_assert!(need_b_lit);
                        /*let pos = self
                            .sat
                            .b_literals
                            .binary_search_by(|elem| elem.0.cmp(&other_clause_id));
                        if pos.is_ok() {
                            let sat_var = self.sat.b_literals[pos.unwrap()].1;
                            inner_equal_to = Some(sat_var);
                            break;
                        }*/
                    }
                }
            }

            if need_t_lit {
                if outer_equal_to.is_none() {
                    let t_lit = self.sat.new_var();
                    sat_clause.push(t_lit);
                    self.sat.t_literals.insert(clause_id as ClauseId, t_lit);
                    self.sat
                        .reverse_t_literals
                        .insert(t_lit.var(), clause_id as ClauseId);
                } else {
                    let t_lit = outer_equal_to.unwrap();
                    sat_clause.push(t_lit);
                    // we don't need to add it to t-literals since it will be already assumed by earlier clause
                    // otherwise, we would assume twice
                    //self.t_literals.push((clause_id as ClauseId, t_lit));
                }
            }

            if need_b_lit {
                let b_lit;
                if inner_equal_to.is_none() {
                    b_lit = self.sat.new_var();
                } else {
                    b_lit = inner_equal_to.unwrap();
                }
                sat_clause.push(!b_lit);
                self.sat.b_literals.insert(clause_id as ClauseId, b_lit);
            }

            debug_assert!(!sat_clause.is_empty());
            self.sat.sat.add_clause(sat_clause.as_ref());
            sat_clause.clear();

            if !contains_inner_var {
                debug_assert!(contains_variables);
                self.max_clauses.set(clause_id, true);
            }
        }

        debug!("Scope {} with level {}", scope.id, scope.level);
        debug!("t-literals: {}", self.sat.t_literals.len());
        debug!("b-literals: {}", self.sat.b_literals.len());

        #[cfg(debug_assertions)]
        {
            let mut t_literals = String::new();
            for (&clause_id, _) in self.sat.t_literals.iter() {
                t_literals.push_str(&format!(" t{}", clause_id));
            }
            debug!("t-literals: {}", t_literals);

            let mut b_literals = String::new();
            for (&clause_id, _) in self.sat.b_literals.iter() {
                b_literals.push_str(&format!(" b{}", clause_id));
            }
            debug!("b-literals: {}", b_literals);
        }
    }

    fn new_universal(&mut self, matrix: &QMatrix, options: &CaqeSolverOptions, scope: &Scope) {
        // build SAT instance for negation of clauses, i.e., basically we only build binary clauses
        'next_clause: for (clause_id, clause) in matrix.clauses.iter().enumerate() {
            debug_assert!(clause.len() != 0, "unit clauses indicate a problem");

            let clause_id = clause_id as ClauseId;

            let mut levels = MinMax::new();

            // check if there is at most one variable bound in current level (and no outer variables)
            // then one can replace the b-literal by the variable itself
            let mut single_literal = None;
            let mut num_scope_variables = 0;
            for &literal in clause.iter() {
                let var_level = matrix.prefix.variables().get(literal.variable()).level;
                levels.update(var_level);
                if !self.sat.variable_to_sat.contains_key(&literal.variable()) {
                    continue;
                }
                self.relevant_clauses.set(clause_id as usize, true);
                num_scope_variables += 1;
                if single_literal.is_none() {
                    single_literal = Some(literal);
                }
            }
            let (min_level, max_level) = levels.get();

            // We check whether the clause is equal to a prior clause w.r.t. outer and current variables.
            // In this case, we can re-use the b-literal from other clause (and can omit t-literal all together).
            if options.abstraction_literal_optimization
                && single_literal.is_some()
                && (num_scope_variables > 1 || min_level < scope.level)
            {
                let literal = single_literal.unwrap();
                // iterate only over prior clauses
                for &other_clause_id in matrix
                    .occurrences(literal)
                    .filter(|&&id| id < clause_id as ClauseId)
                {
                    let other_clause = &matrix.clauses[other_clause_id as usize];
                    if clause.is_equal_wrt_predicate(other_clause, |l| {
                        let info = matrix.prefix.variables().get(l.variable());
                        info.level <= scope.level
                    }) {
                        let sat_var = self.sat.b_literals.get(&other_clause_id).unwrap();
                        self.sat.b_literals.insert(clause_id as ClauseId, *sat_var);
                        continue 'next_clause;
                    }
                }
            }

            let sat_var;

            // there is a single literal and no outer variables, replace t-literal by literal
            if options.abstraction_literal_optimization
                && num_scope_variables == 1
                && min_level == scope.level
            {
                let literal = single_literal.unwrap();
                sat_var = !self.sat.lit_to_sat_lit(literal);
            } else if num_scope_variables > 0 {
                // build abstraction
                sat_var = self.sat.new_var();
                for &literal in clause.iter() {
                    if !self.sat.variable_to_sat.contains_key(&literal.variable()) {
                        continue;
                    }
                    let lit = self.sat.lit_to_sat_lit(literal);
                    self.sat.sat.add_clause(&[!sat_var, !lit]);
                }
            } else {
                // no variable of current scope
                // do not add t-literal nor b-literal, we adapt abstraction during solving if needed
                continue;
            }

            debug_assert!(self.relevant_clauses[clause_id as usize]);

            let need_t_lit = min_level < scope.level && scope.level <= max_level;
            let need_b_lit = min_level <= scope.level && scope.level <= max_level;

            debug_assert!(min_level <= scope.level);
            debug_assert!(max_level >= scope.level);

            if need_t_lit {
                self.sat.t_literals.insert(clause_id as ClauseId, sat_var);
                debug_assert!(!self.sat.reverse_t_literals.contains_key(&sat_var.var()));
                self.sat
                    .reverse_t_literals
                    .insert(sat_var.var(), clause_id as ClauseId);
            }

            if need_b_lit {
                self.sat.b_literals.insert(clause_id as ClauseId, sat_var);
            }

            if min_level == scope.level {
                self.max_clauses.set(clause_id as usize, true);
            }
        }

        debug!("Scope {} with level {}", scope.id, scope.level);
        debug!("t-literals: {}", self.sat.t_literals.len());
        debug!("b-literals: {}", self.sat.b_literals.len());

        #[cfg(debug_assertions)]
        {
            let mut t_literals = String::new();
            for (&clause_id, _) in self.sat.t_literals.iter() {
                t_literals.push_str(&format!(" t{}", clause_id));
            }
            debug!("t-literals: {}", t_literals);

            let mut b_literals = String::new();
            for (&clause_id, _) in self.sat.b_literals.iter() {
                b_literals.push_str(&format!(" b{}", clause_id));
            }
            debug!("b-literals: {}", b_literals);
        }
    }

    fn check_candidate_exists(&mut self, next: &mut Vec<Box<ScopeRecursiveSolver>>) -> Lbool {
        // we need to reset abstraction entries for next scopes, since some entries may be pushed down
        self.entry.intersect(&self.relevant_clauses);
        for ref mut scope in next {
            scope.data.entry.clone_from(&self.entry);
        }

        self.sat_solver_assumptions.clear();

        #[cfg(debug_assertions)]
        let mut debug_print = String::new();

        // we iterate in parallel over the entry and the t-literals of current level
        // there are 3 possibilities:
        // * clause from entry is not a t-lit: push entry to next quantifier
        // * clause is in entry and a t-lit: assume positively
        // * clause is not in entry and a t-lit: assume negatively
        for (&clause_id, &t_literal) in self.sat.t_literals.iter() {
            let mut t_literal = t_literal;
            if !self.entry[clause_id as usize] {
                t_literal = !t_literal;
            }
            if self.is_universal {
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

            if self.is_universal && !t_literal.isneg() {
                // assume t-literal completely for existential quantifier
                // and only negatively for universal quantifier
                continue;
            }

            self.sat_solver_assumptions.push(t_literal);
        }

        #[cfg(debug_assertions)]
        debug!("assume {}", debug_print);

        self.sat
            .solve_with_assumptions(self.sat_solver_assumptions.as_ref())
    }

    fn update_assignment(&mut self) {
        trace!("update_assignment");

        #[cfg(debug_assertions)]
        let mut debug_print = String::new();

        let model = self.sat.get_model();
        for (&variable, &sat_var) in self.sat.variable_to_sat.iter() {
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

            let old = self.assignments.entry(variable).or_insert(value);
            *old = value;
        }

        #[cfg(debug_assertions)]
        debug!("assignment {}", debug_print);
    }

    fn get_assumptions(&mut self, matrix: &QMatrix, next: &mut Vec<Box<ScopeRecursiveSolver>>) {
        trace!("get_assumptions");

        // assumptions in `next` were already cleared in check_candidate_exists

        #[cfg(debug_assertions)]
        let mut debug_print = String::new();

        if !self.is_universal {
            for (&clause_id, &b_lit) in self.sat.b_literals.iter() {
                if self.sat.sat.is_true(b_lit) {
                    next.iter_mut().for_each(|ref mut scope| {
                        scope.data.entry.set(clause_id as usize, true);
                    });
                    continue;
                }
                /*debug_assert!(
                    !self.entry[clause_id as usize] || assumptions[clause_id as usize],
                    "entry -> assumption"
                );*/

                if self.entry[clause_id as usize] {
                    //debug_assert!(assumptions[clause_id as usize]);
                    continue;
                }

                // assumption literal was set, but it may be still true that the clause is satisfied
                let clause = &matrix.clauses[clause_id as usize];
                if clause.is_satisfied_by_assignment(&self.assignments) {
                    next.iter_mut().for_each(|ref mut scope| {
                        scope.data.entry.set(clause_id as usize, true);
                    });
                    continue;
                }

                #[cfg(debug_assertions)]
                debug_print.push_str(&format!(" b{}", clause_id));
            }
        } else {
            for (&clause_id, &b_lit) in self.sat.b_literals.iter() {
                if self.sat.sat.is_true(b_lit) {
                    continue;
                }

                // assumption literal was set
                // check if clause is falsified by current level
                let clause = &matrix.clauses[clause_id as usize];
                let mut falsified = true;
                let mut nonempty = false;

                for literal in clause.iter() {
                    if !self.sat.variable_to_sat.contains_key(&literal.variable()) {
                        // not a variable of current level
                        continue;
                    }
                    nonempty = true;
                    let value = self.assignments[&literal.variable()];
                    if value && !literal.signed() || !value && literal.signed() {
                        falsified = false;
                        break;
                    }
                }
                if nonempty && falsified {
                    // depending on t-literal, the assumption is already set
                    continue;
                    /*if self.t_literals.contains_key(&clause_id) {
                        if !self.entry[clause_id as usize] {
                            continue;
                        }
                    } else {
                        continue;
                    }*/
                }
                if !nonempty {
                    debug_assert!(self.sat.t_literals.get(&clause_id).is_some());
                    // we have already copied the value by copying current entry
                    continue;
                    /*if !self.entry[clause_id as usize] {
                        continue;
                    }*/
                }

                next.iter_mut().for_each(|ref mut scope| {
                    scope.data.entry.set(clause_id as usize, true);
                });

                #[cfg(debug_assertions)]
                debug_print.push_str(&format!(" b{}", clause_id));
            }
        }

        #[cfg(debug_assertions)]
        debug!("assumptions: {}", debug_print);
    }

    fn entry_minimization(&mut self, matrix: &QMatrix) {
        trace!("entry_minimization");

        // add clauses to entry where the current scope is maximal
        self.entry.union(&self.max_clauses);

        for variable in self.variables.iter() {
            let value = self.assignments[variable];
            let literal = Literal::new(*variable, !value);

            // check if assignment is needed, i.e., it can flip a bit in entry
            let mut needed = false;
            for &clause_id in matrix.occurrences(literal) {
                if clause_id as usize >= self.entry.len() {
                    // clause was added to matrix but is not yet contained in solver
                    continue;
                }

                if self.entry[clause_id as usize] {
                    needed = true;
                    self.entry.set(clause_id as usize, false);
                }
            }

            if !needed {
                // the current value set is not needed for the entry, try other polarity
                for &clause_id in matrix.occurrences(-literal) {
                    if clause_id as usize >= self.entry.len() {
                        // clause was added to matrix but is not yet contained in solver
                        continue;
                    }
                    if self.entry[clause_id as usize] {
                        self.entry.set(clause_id as usize, false);
                    }
                }
            }
        }

        #[cfg(debug_assertions)]
        for (i, _val) in self.entry.iter().enumerate().filter(|&(_, val)| val) {
            let clause = &matrix.clauses[i];
            let mut min = std::u32::MAX;
            for &literal in clause.iter() {
                let otherscope = matrix.prefix.variables().get(literal.variable()).level;
                if otherscope < min {
                    min = otherscope;
                }
            }
            assert!(min < self.level);
        }
    }

    fn is_influenced_by_witness(&self, matrix: &QMatrix, next: &mut ScopeRecursiveSolver) -> bool {
        trace!("is_influenced_by_witness");

        // witness
        let entry = &next.data.entry;

        // check if influenced by current scope
        for (i, _) in entry.iter().enumerate().filter(|&(_, val)| val) {
            let clause = &matrix.clauses[i];

            for &literal in clause.iter() {
                let other_scope_id = matrix.prefix.variables().get(literal.variable()).scope_id;
                if other_scope_id.expect("variable is bound") == self.scope_id {
                    return true;
                }
                debug_assert!(!self.variables.contains(&literal.variable()));
            }
        }
        false
    }

    fn refine(
        &mut self,
        matrix: &QMatrix,
        next: &mut ScopeRecursiveSolver,
        global: &mut GlobalSolverData,
    ) {
        trace!("refine");

        let options = &global.options;
        let conflicts = &mut global.conflicts;

        // store entry in conflicts
        conflicts.push((next.data.entry.clone(), self.level));

        if options.expansion_refinement && self.is_expansion_refinement_applicable(next) {
            self.expansion_refinement(matrix, options, next, conflicts);
        }

        if !self.is_universal
            && options.strong_unsat_refinement
            && self.strong_unsat_refinement(matrix, next)
        {
            return;
        }
        // important: refinement literal subsumption has to be after strong unsat refinement
        if options.refinement_literal_subsumption {
            self.refinement_literal_subsumption_optimization(matrix, next);
        }

        let entry = &next.data.entry;
        let blocking_clause = &mut self.sat_solver_assumptions;
        blocking_clause.clear();

        #[cfg(debug_assertions)]
        let mut debug_print = String::new();

        for (i, _) in entry.iter().enumerate().filter(|&(_, val)| val) {
            let clause_id = i as ClauseId;
            let b_lit = self.sat.add_b_lit_and_adapt_abstraction(clause_id);
            blocking_clause.push(b_lit);

            #[cfg(debug_assertions)]
            debug_print.push_str(&format!(" b{}", clause_id));
        }
        self.sat.add_clause(blocking_clause.as_ref());

        #[cfg(debug_assertions)]
        debug!("refinement: {}", debug_print);
    }

    /// Implements the strong unsat refinement operation.
    /// If successful, it can reduce the number of iterations needed.
    /// Returns true, if the optimization was applied, false otherwise.
    fn strong_unsat_refinement(
        &mut self,
        matrix: &QMatrix,
        next: &mut ScopeRecursiveSolver,
    ) -> bool {
        trace!("strong_unsat_refinement");
        debug_assert!(!self.is_universal);
        let mut applied = false;

        // re-use sat-solver-assumptions vector
        let blocking_clause = &mut self.sat_solver_assumptions;
        blocking_clause.clear();

        let entry = &next.data.entry;
        let level = self.level;

        // was the clause processed before?
        for (i, _) in entry.iter().enumerate().filter(|&(_, val)| val) {
            let clause_id = i as ClauseId;
            match self.strong_unsat_cache.get(&clause_id) {
                Some(&(literal, opt)) => {
                    if opt {
                        applied = true;
                    }
                    blocking_clause.push(literal);
                    continue;
                }
                None => {}
            }

            // TODO: for implementation of stronger unsat rule (see "On Expansion and Resolution in CEGAR Based QBF Solving"),
            // we have to collect all universal variables from all failed clauses.
            // This means espacially that we cannot use our current hashing anymore

            // Get some random existential occurrence from clause, so we can use
            // the occurrence list to iterate over clauses
            let clause = &matrix.clauses[i];
            self.conjunction.clear();
            self.conjunction.push(clause_id);
            for &literal in clause.iter() {
                let info = matrix.prefix.variables().get(literal.variable());

                // Consider only existential variables that have a lower level
                if info.is_universal() || info.level <= self.level {
                    continue;
                }

                // Iterate over occurrence list and add equivalent clauses
                for &other_clause_id in matrix.occurrences(literal) {
                    if other_clause_id as usize >= self.relevant_clauses.len() {
                        // clause was added to matrix but not yet contained in solver
                        continue;
                    }
                    let other_clause = &matrix.clauses[other_clause_id as usize];
                    // check if clause is subset w.r.t. inner variables
                    if clause_id != other_clause_id
                        && self.relevant_clauses[other_clause_id as usize]
                    {
                        let pos = match self.conjunction.binary_search(&other_clause_id) {
                            Ok(_) => continue, // already contained, skip
                            Err(pos) => pos,   // position to insert
                        };

                        if other_clause.is_subset_wrt_predicate(clause, |l| {
                            matrix.prefix.variables().get(l.variable()).level > level
                        }) {
                            debug_assert!(!self.max_clauses[other_clause_id as usize]);
                            self.conjunction.insert(pos, other_clause_id);
                        }
                    }
                }
            }

            debug_assert!(self.conjunction.len() > 0);
            if self.conjunction.len() == 1 {
                // do not need auxilliary variable
                let clause_id = self.conjunction[0];
                let sat_lit = self.sat.add_b_lit_and_adapt_abstraction(clause_id);
                blocking_clause.push(sat_lit);
                self.strong_unsat_cache.insert(clause_id, (sat_lit, false));
            } else {
                // build the conjunction using an auxilliary variable
                let aux_var = self.sat.new_var();
                blocking_clause.push(aux_var);
                self.strong_unsat_cache.insert(clause_id, (aux_var, true));

                for &other_clause_id in self.conjunction.iter() {
                    let sat_lit = self.sat.add_b_lit_and_adapt_abstraction(other_clause_id);
                    self.sat.add_clause(&[!aux_var, sat_lit]);
                }
                applied = true;
            }
        }

        if applied {
            self.sat.add_clause(blocking_clause.as_ref());
        }

        applied
    }

    /// Tries to reduce the size of refinements.
    /// If a clause is subsumed by another clause in refinement, it can be removed.
    /// This does not change the number of iterations, but may make the job of SAT solver easier.
    ///
    /// Returns true if the refinement clause could be reduced.
    fn refinement_literal_subsumption_optimization(
        &mut self,
        matrix: &QMatrix,
        next: &mut ScopeRecursiveSolver,
    ) -> bool {
        let mut successful = false;
        let entry = &mut next.data.entry;
        'outer: for i in 0..entry.len() {
            if !entry[i] {
                continue;
            }
            let clause_id = i as ClauseId;
            let clause = &matrix.clauses[i];
            for &literal in clause.iter() {
                let info = matrix.prefix.variables().get(literal.variable());
                if info.level > self.level {
                    // do not consider inner variables
                    continue;
                }
                // iterate over occurrence list
                for &other_clause_id in matrix.occurrences(literal) {
                    if clause_id == other_clause_id {
                        continue;
                    }
                    if clause_id as usize >= entry.len() {
                        // clause was added to matrix but is not yet contained in solver
                        continue;
                    }
                    if !entry[other_clause_id as usize] {
                        // not in entry, thus not interesting
                        continue;
                    }
                    let other_clause = &matrix.clauses[other_clause_id as usize];
                    let current_level = self.level;
                    // check if other clause subsumes current
                    // check is done with respect to current and outer variables
                    if self.is_universal {
                        if other_clause.is_subset_wrt_predicate(clause, |l| {
                            let info = matrix.prefix.variables().get(l.variable());
                            info.level <= current_level
                        }) {
                            entry.set(clause_id as usize, false);
                            successful = true;
                            continue 'outer;
                        }
                    } else {
                        if clause.is_subset_wrt_predicate(other_clause, |l| {
                            let info = matrix.prefix.variables().get(l.variable());
                            info.level <= current_level
                        }) {
                            entry.set(clause_id as usize, false);
                            successful = true;
                            continue 'outer;
                        }
                    }
                }
            }
        }
        successful
    }

    fn is_expansion_refinement_applicable(&self, next: &mut ScopeRecursiveSolver) -> bool {
        if self.is_universal {
            return false;
        }
        return true;
        debug_assert_eq!(next.next.len(), 1, "scope {:?}", self.scope_id);
        next.next[0].as_ref().next.is_empty()
    }

    fn expansion_refinement(
        &mut self,
        matrix: &QMatrix,
        options: &CaqeSolverOptions,
        next: &mut ScopeRecursiveSolver,
        conflicts: &mut Vec<(BitVec, u32)>,
    ) {
        trace!("expansion_refinement");
        let universal_assignment = next.get_universal_assignmemnt(FxHashMap::default());
        let (data, next) = next.split();
        debug_assert!(data.is_universal);
        debug_assert_eq!(next.len(), 1);
        let next = &next[0];

        // create the refinement clauses
        for (i, clause) in matrix.clauses.iter().enumerate() {
            if i >= next.data.relevant_clauses.len() {
                // clause was added to matrix, but not yet contained in solver
                continue;
            }
            if !next.data.relevant_clauses[i] {
                continue;
            }

            self.expand_clause(matrix, i as ClauseId, clause, &universal_assignment);
        }

        if !options.conflict_clause_expansion {
            return;
        }

        // build expansions for new conflict clauses and previous assignments (not including the current one)
        if self.next_conflict < conflicts.len() {
            for conflict in conflicts.split_at(self.next_conflict).1 {
                if conflict.1 <= self.level {
                    continue;
                }
                for i in 0..self.expansions.len() {
                    self.expand_conflict_clause(matrix, data, &conflict.0, i);
                }
            }
        }

        self.expansions.push(universal_assignment);

        // build expansions for all conflict clauses with current assignment
        for conflict in conflicts.iter() {
            self.expand_conflict_clause(matrix, data, &conflict.0, self.expansions.len() - 1);
        }

        self.next_conflict = conflicts.len();
    }

    fn expand_clause(
        &mut self,
        matrix: &QMatrix,
        clause_id: ClauseId,
        clause: &Clause,
        universal_assignment: &FxHashMap<Variable, bool>,
    ) {
        // check if the universal assignment satisfies the clause
        if clause.is_satisfied_by_assignment(&universal_assignment) {
            return;
        }

        let sat = &mut self.sat;
        let sat_clause = &mut self.sat_solver_assumptions;
        sat_clause.clear();

        // add the clause to the abstraction
        // variables bound by inner existential quantifier have to be renamed
        let mut contains_variables = false;
        let mut contains_outer_variables = false;
        for &literal in clause.iter() {
            let info = matrix.prefix.variables().get(literal.variable());
            if info.level <= self.level {
                // below or equal to the current existential quantifier
                if info.level < self.level {
                    // strictly smaller than current existential quantifier
                    contains_outer_variables = true;
                }
                // ignore variables
                continue;
            }
            if info.is_universal() {
                // every inner universal variable is contained in the assignment
                debug_assert!(universal_assignment.contains_key(&literal.variable()));
                continue;
            }
            debug_assert!(info.level > self.level);
            debug_assert!(info.is_existential());
            contains_variables = true;

            // porject universal assignment to dependencies of variable
            let mut deps: Vec<Literal> = universal_assignment
                .iter()
                .filter(|(var, _val)| info.dependencies().contains(var))
                .map(|(&var, val)| Literal::new(var, !val))
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
            sat_clause.push(sat_var);
        }

        if !contains_variables {
            // no inner variables, thus, expansion does not bring a benefit
            return;
        }
        debug_assert!(contains_variables);
        // need to add a b-literal if there are inner and outer variables but not necisarilly of current quantifier
        // note that it cannot happen that there are variables of the current quantifier but no b-literal, because in this case, there are no inner variables
        if sat.b_literals.get(&clause_id).is_some()
            || contains_variables && contains_outer_variables
        {
            let sat_lit = sat.add_b_lit_and_adapt_abstraction(clause_id);
            sat_clause.push(sat_lit);
        }

        if !sat_clause.is_empty() {
            sat.add_clause(sat_clause.as_ref());
        }
    }

    fn expand_conflict_clause(
        &mut self,
        matrix: &QMatrix,
        data: &ScopeSolverData,
        conflict: &BitVec,
        universal_assignment: usize,
    ) {
        debug_assert!(data.is_universal);

        let sat = &mut self.sat;
        let sat_clause = &mut self.sat_solver_assumptions;
        sat_clause.clear();

        // get next scope to determine relevant scopes
        let next_scope_id = matrix.prefix.next_scopes[self.scope_id.to_usize()]
            .iter()
            .skip_while(|s| **s != data.scope_id)
            .skip_while(|s| **s == data.scope_id)
            .next();

        let universal_assignment = &self.expansions[universal_assignment];

        // build expansion for conflict clause
        let mut contains_variables = false;
        let mut contains_outer_variables = false;
        let mut is_satisfied = false;
        for (i, _) in conflict.iter().enumerate().filter(|&(_, val)| val) {
            let clause = &matrix.clauses[i];

            // check if the universal assignment satisfies the clause
            if clause.is_satisfied_by_assignment(&universal_assignment) {
                is_satisfied = true;
                break;
            }

            // add the clause to the abstraction
            // variables bound by inner existential quantifier have to be renamed

            for &literal in clause.iter() {
                let info = matrix.prefix.variables().get(literal.variable());
                if info.level <= self.level {
                    // below or equal to the current existential quantifier
                    if info.level < self.level {
                        // strictly smaller than current existential quantifier
                        contains_outer_variables = true;
                    }
                    // ignore variables
                    continue;
                }
                if info.is_universal() {
                    // every inner universal variable is contained in the assignment
                    //assert!(universal_assignment.contains_key(&literal.variable()));
                    continue;
                }
                if info.scope_id.unwrap() < data.scope_id {
                    // not relevant for the current assignment
                    continue;
                }
                if let Some(next) = next_scope_id {
                    if info.scope_id.unwrap() >= *next {
                        // not relevant for the current assignment
                        continue;
                    }
                }
                debug_assert!(info.level > self.level);
                debug_assert!(info.is_existential());
                contains_variables = true;

                // porject universal assignment to dependencies of variable
                let mut deps: Vec<Literal> = universal_assignment
                    .iter()
                    .filter(|(var, _val)| info.dependencies().contains(var))
                    .map(|(&var, val)| Literal::new(var, !val))
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
                sat_clause.push(sat_var);
            }
            let clause_id = i as ClauseId;
            if !contains_variables {
                continue;
            }
            if sat.b_literals.get(&clause_id).is_some()
                || contains_variables && contains_outer_variables
            {
                let sat_lit = sat.add_b_lit_and_adapt_abstraction(clause_id);
                sat_clause.push(sat_lit);
            }
        }

        if !is_satisfied && !sat_clause.is_empty() {
            sat.add_clause(sat_clause.as_ref());
        }
    }

    fn get_unsat_core(&mut self) {
        trace!("unsat_core");

        self.entry.clear();

        #[cfg(debug_assertions)]
        let mut debug_print = String::new();

        let failed = self.sat.get_conflict();
        for l in failed {
            let clause_id = self.sat.reverse_t_literals[&l.var()];
            self.entry.set(clause_id as usize, true);

            #[cfg(debug_assertions)]
            debug_print.push_str(&format!(" t{}", clause_id));
        }

        #[cfg(debug_assertions)]
        debug!("unsat core: {}", debug_print);
    }

    /// filters those clauses that are only influenced by this quantifier (or inner)
    fn unsat_propagation(&mut self) {
        self.entry.difference(&self.max_clauses);
    }

    /// Extracts conflict clause from entry
    fn extract_conflict_clause(
        &mut self,
        matrix: &mut QMatrix,
        next: &mut Box<ScopeRecursiveSolver>,
    ) {
        if self.is_universal {
            return;
        }
        trace!("extract_conflict_clause");

        let mut literals = Vec::new();

        // extract conflict clause from entry
        let entry = &next.data.entry;

        for (i, _) in entry.iter().enumerate().filter(|&(_, val)| val) {
            let clause = &matrix.clauses[i];
            for &literal in clause.iter() {
                let info = matrix.prefix.variables().get(literal.variable());
                if info.level > self.level {
                    continue;
                }
                literals.push(literal);
            }
        }
        debug!("conflict clause {:?}", literals);
        matrix.add(Clause::new(literals));
    }
}

struct MinMax {
    min: Option<u32>,
    max: Option<u32>,
}

impl MinMax {
    fn new() -> MinMax {
        MinMax {
            min: None,
            max: None,
        }
    }

    fn update(&mut self, value: u32) {
        match (self.min, self.max) {
            (None, None) => {
                self.min = Some(value);
                self.max = Some(value);
            }
            (Some(min), Some(max)) => {
                if value < min {
                    self.min = Some(value);
                }
                if value > max {
                    self.max = Some(value);
                }
            }
            _ => panic!("inconsistent internal state"),
        }
    }

    fn min(&self) -> u32 {
        self.min.unwrap()
    }

    fn max(&self) -> u32 {
        self.max.unwrap()
    }

    fn get(&self) -> (u32, u32) {
        (self.min(), self.max())
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::solve::Solver;

    #[test]
    fn test_false() {
        let instance = "p cnf 0 1\n0\n";
        let matrix = qdimacs::parse(&instance).unwrap();
        assert!(matrix.conflict());
    }

    #[test]
    fn test_true() {
        let instance = "p cnf 0 0";
        let mut matrix = qdimacs::parse(&instance).unwrap();
        matrix.unprenex_by_miniscoping();
        let mut solver = CaqeSolver::new(&mut matrix);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        assert_eq!(solver.qdimacs_output().dimacs(), "s cnf 1 0 0\n");
    }

    #[test]
    fn test_sat_simple() {
        let instance = "c
p cnf 4 4
a 1 2 0
e 3 4 0
1 3 0
-1 4 0
-3 -4 0
-1 2 4 0
";
        let mut matrix = parse::qdimacs::parse(&instance).unwrap();
        matrix.unprenex_by_miniscoping();
        let mut solver = CaqeSolver::new(&mut matrix);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        assert_eq!(solver.qdimacs_output().dimacs(), "s cnf 1 4 4\n");
    }

    #[test]
    fn test_unsat_simple() {
        let instance = "c
p cnf 4 4
a 1 2 0
e 3 4 0
1 3 0
-1 4 0
-3 -4 0
1 2 4 0
";
        let mut matrix = parse::qdimacs::parse(&instance).unwrap();
        matrix.unprenex_by_miniscoping();
        let mut solver = CaqeSolver::new(&mut matrix);
        assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
        assert_eq!(
            solver.qdimacs_output().dimacs(),
            "s cnf 0 4 4\nV -1 0\nV -2 0\n"
        );
    }

    #[test]
    fn test_two_alternations() {
        let instance = "c
p cnf 11 24
a 1 0
e 2 0
a 3 0
e 4 5 6 7 8 9 10 11 0
3 5 0
-4 5 0
-3 4 -5 0
-3 6 0
4 6 0
3 -4 -6 0
2 -7 0
5 -7 0
6 -7 0
-2 -5 -6 7 0
-1 8 0
-7 8 0
1 7 -8 0
-2 -9 0
5 -9 0
6 -9 0
2 -5 -6 9 0
1 10 0
-9 10 0
-1 9 -10 0
8 -11 0
10 -11 0
-8 -10 11 0
11 0
";
        let mut matrix = parse::qdimacs::parse(&instance).unwrap();
        matrix.unprenex_by_miniscoping();
        let mut solver = CaqeSolver::new(&mut matrix);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        assert_eq!(solver.qdimacs_output().dimacs(), "s cnf 1 11 24\n");
    }

    #[test]
    fn test_wrong_sat() {
        let instance = "c
c This instance was falsly characterized as SAT
p cnf 4 3
a 4 0
e 3 0
a 1 0
e 2 0
-3 0
3 -4 0
-2 -1 0
";
        let mut matrix = parse::qdimacs::parse(&instance).unwrap();
        matrix.unprenex_by_miniscoping();
        let mut solver = CaqeSolver::new(&mut matrix);
        assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
        assert_eq!(solver.qdimacs_output().dimacs(), "s cnf 0 4 3\nV 4 0\n");
    }

    #[test]
    fn test_cnf() {
        let instance = "c
c CNF instance without quantifier
p cnf 1 2
-1 0
1 0
";
        let mut matrix = parse::qdimacs::parse(&instance).unwrap();
        matrix.unprenex_by_miniscoping();
        let mut solver = CaqeSolver::new(&mut matrix);
        assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
        assert_eq!(solver.qdimacs_output().dimacs(), "s cnf 0 1 2\n");
    }

    #[test]
    fn test_wrong_unsat() {
        let instance = "c
c This instance was falsly characterized as UNSAT
p cnf 3 2
a 1 2 0
e 3 0
3 -2 0
-3 -1 2 0
";
        let mut matrix = parse::qdimacs::parse(&instance).unwrap();
        matrix.unprenex_by_miniscoping();
        let mut solver = CaqeSolver::new(&mut matrix);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        assert_eq!(solver.qdimacs_output().dimacs(), "s cnf 1 3 2\n");
    }

    #[test]
    fn test_strong_unsat_crash() {
        let instance = "c
c This instance crashed with strong unsat refinement
p cnf 4 3
a 2 0
e 1 0
a 4 0
e 3 0
1 3 0
-3 -2 0
3 -4 0
";
        let mut matrix = parse::qdimacs::parse(&instance).unwrap();
        matrix.unprenex_by_miniscoping();
        let mut solver = CaqeSolver::new(&mut matrix);
        assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
        assert_eq!(solver.qdimacs_output().dimacs(), "s cnf 0 4 3\nV 2 0\n");
    }

    #[test]
    fn test_refinement_literal_failure() {
        let instance = "c
c This instance was solved incorrectly in earlier versions due to refinement literal optimization
p cnf 5 5
a 5 0
e 3 0
a 1 0
e 2 4 0
-2 0
4 5 0
-4 -5 0
-4 -5 -1 0
2 3 0
";
        let mut matrix = parse::qdimacs::parse(&instance).unwrap();
        matrix.unprenex_by_miniscoping();
        let mut solver = CaqeSolver::new(&mut matrix);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        assert_eq!(solver.qdimacs_output().dimacs(), "s cnf 1 5 5\n");
    }

    #[test]
    fn test_refinement_literal_failure2() {
        let instance = "c
c This instance was solved incorrectly in earlier versions due to refinement literal optimization
p cnf 4 3
a 4 0
e 1 0
a 3 0
e 2 0
-2 0
2 -3 -4 0
-1 -4 0
";
        let mut matrix = parse::qdimacs::parse(&instance).unwrap();
        matrix.unprenex_by_miniscoping();
        let mut solver = CaqeSolver::new(&mut matrix);
        assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
        assert_eq!(solver.qdimacs_output().dimacs(), "s cnf 0 4 3\nV 4 0\n");
    }

    #[test]
    fn test_abstraction_literal_optimization_vs_strong_unsat() {
        let instance = "c
c This instance was solved incorrectly in earlier versions due to abstraction literal optimization
p cnf 3 4
e 3 0
a 1 0
e 2 0
-2 -1 0
-2 0
-2 3 0
3 2 0
";
        let mut matrix = parse::qdimacs::parse(&instance).unwrap();
        matrix.unprenex_by_miniscoping();
        let mut solver = CaqeSolver::new(&mut matrix);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        assert_eq!(solver.qdimacs_output().dimacs(), "s cnf 1 3 4\nV 3 0\n");
    }

    #[test]
    fn test_strong_unsat_failure() {
        let instance = "c
c This instance was solved incorrectly in earlier versions due to strong unsat refinement.
c The strong unsat refinement can only applied to clauses which actually contains inner variables.
p cnf 4 3
e 2 3 0
a 4 0
e 1 0
-1 0
-2 3 0
3 1 -4 0
";
        let mut matrix = parse::qdimacs::parse(&instance).unwrap();
        matrix.unprenex_by_miniscoping();
        let mut solver = CaqeSolver::new(&mut matrix);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        assert_eq!(
            solver.qdimacs_output().dimacs(),
            "s cnf 1 4 3\nV -2 0\nV 3 0\n"
        );
    }

    #[test]
    fn test_fuzz_unsat() {
        let instance = "c
c This instance was solved incorrectly in earlier versions.
p cnf 5 5
e 1 5 0
a 4 0
e 2 3 0
-5 1 3 0
1 -5 0
-1 0
-2 4 0
5 0
";
        let mut matrix = parse::qdimacs::parse(&instance).unwrap();
        matrix.unprenex_by_miniscoping();
        let mut solver = CaqeSolver::new(&mut matrix);
        assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
        assert_eq!(solver.qdimacs_output().dimacs(), "s cnf 0 5 5\n");
    }

    #[test]
    fn test_fuzz_sat() {
        let instance = "c
c This instance was solved incorrectly in earlier versions.
p cnf 4 4
e 2 0
a 4 0
e 1 3 0
1 0
2 1 0
3 -4 0
-3 2 0
";
        let mut matrix = parse::qdimacs::parse(&instance).unwrap();
        matrix.unprenex_by_miniscoping();
        let mut solver = CaqeSolver::new(&mut matrix);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        assert_eq!(solver.qdimacs_output().dimacs(), "s cnf 1 4 4\nV 2 0\n");
    }

    #[test]
    fn test_wrong_unsat_miniscoping() {
        let instance = "c
c This instance was solved incorrectly in earlier versions.
p cnf 4 4
e 4 0
a 2 0
e 1 3 0
4 1 0
-1 0
4 -3 0
1 2 0
";
        let mut matrix = parse::qdimacs::parse(&instance).unwrap();
        matrix.unprenex_by_miniscoping();
        let mut solver = CaqeSolver::new(&mut matrix);
        assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
        assert_eq!(solver.qdimacs_output().dimacs(), "s cnf 0 4 4\n");
    }

    #[test]
    fn test_wrong_expansion_refinement() {
        let instance = "c
c This instance was solved incorrectly in earlier versions.
c The first conflict happens at level 2, then expansion refinement did not have universal assignments for level 3
p cnf 7 6
e 7 0
a 4 0
e 2 6 0
a 5 0
e 1 3 0
-3 5 0
3 -5 0
2 0
6 4 0
-2 7 0
-3 -2 -1 0
";
        let mut matrix = parse::qdimacs::parse(&instance).unwrap();
        matrix.unprenex_by_miniscoping();
        let mut solver = CaqeSolver::new(&mut matrix);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        assert_eq!(solver.qdimacs_output().dimacs(), "s cnf 1 7 6\nV 7 0\n");
    }

    #[test]
    fn test_strong_unsat_failure_2() {
        let instance = "c
c This instance was solved incorrectly in earlier versions.
p cnf 5 4
e 1 0
a 3 0
e 4 0
a 5 0
e 2 0
-2 0
-2 1 -4 3 -5 0
4 0
-4 2 1 3 0
";
        let mut matrix = parse::qdimacs::parse(&instance).unwrap();
        matrix.unprenex_by_miniscoping();
        let mut solver = CaqeSolver::new(&mut matrix);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        assert_eq!(solver.qdimacs_output().dimacs(), "s cnf 1 5 4\nV 1 0\n");
    }

    #[test]
    fn test_miniscoping_regression() {
        let instance = "c
c This instance was solved incorrectly in earlier versions.
p cnf 8 5
e 1 6 0
a 5 0
e 2 4 0
a 3 0
e 7 8 0
-8 0
-2 0
-6 -7 5 0
7 -3 0
4 1 0
";
        let mut matrix = parse::qdimacs::parse(&instance).unwrap();
        matrix.unprenex_by_miniscoping();
        let mut solver = CaqeSolver::new(&mut matrix);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        assert_eq!(
            solver.qdimacs_output().dimacs(),
            "s cnf 1 8 5\nV -1 0\nV 4 0\nV -5 0\nV -6 0\nV -8 0\n"
        );
    }
}
