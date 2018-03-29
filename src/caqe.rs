extern crate cryptominisat;
use self::cryptominisat::*;

use super::*;

use std::collections::HashMap;

type ClauseId = u32;

type QMatrix = Matrix<HierarchicalPrefix>;

pub struct CaqeSolver<'a> {
    matrix: &'a QMatrix,
    abstraction: Box<CandidateGeneration>,
}

impl<'a> CaqeSolver<'a> {
    pub fn new(matrix: &'a QMatrix) -> CaqeSolver {
        CaqeSolver {
            matrix: matrix,
            abstraction: CandidateGeneration::init_abstraction_recursively(matrix, 0),
        }
    }
}

impl<'a> super::Solver for CaqeSolver<'a> {
    fn solve(&mut self) -> SolverResult {
        self.abstraction.as_mut().solve_recursive(self.matrix)
    }
}

struct CandidateGeneration {
    sat: cryptominisat::Solver,
    variable_to_sat: HashMap<Variable, Lit>,
    t_literals: HashMap<ClauseId, Lit>,
    b_literals: HashMap<ClauseId, Lit>,

    /// lookup from sat solver variables to clause id's
    reverse_t_literals: HashMap<u32, ClauseId>,

    assignments: HashMap<Variable, bool>,

    /// stores for every clause whether the clause is satisfied or not by assignments to outer variables
    entry: Vec<bool>,

    min_entry: Vec<bool>,

    /// stores the assumptions (as clause id's) given to sat solver
    sat_solver_assumptions: Vec<ClauseId>,

    is_universal: bool,
    scope_id: ScopeId,

    next: Option<Box<CandidateGeneration>>,
}

impl CandidateGeneration {
    fn new(
        matrix: &QMatrix,
        scope: &Scope,
        quantifier: Quantifier,
        next: Option<Box<CandidateGeneration>>,
    ) -> CandidateGeneration {
        let mut entry = Vec::new();
        entry.resize(matrix.clauses.len(), false);
        let mut candidate = CandidateGeneration {
            sat: cryptominisat::Solver::new(),
            variable_to_sat: HashMap::new(),
            t_literals: HashMap::new(),
            b_literals: HashMap::new(),
            reverse_t_literals: HashMap::new(),
            assignments: HashMap::new(),
            min_entry: entry.clone(),
            entry: entry,
            sat_solver_assumptions: Vec::new(),
            is_universal: scope.id % 2 != 0,
            scope_id: scope.id,
            next: next,
        };

        // add variables of scope to sat solver
        for &variable in scope.variables.iter() {
            candidate
                .variable_to_sat
                .insert(variable, candidate.sat.new_var());
        }

        match quantifier {
            Quantifier::Existential => candidate.new_existential(matrix, scope),
            Quantifier::Universal => candidate.new_universal(matrix, scope),
        }

        candidate
    }

    fn init_abstraction_recursively(
        matrix: &QMatrix,
        scope_id: ScopeId,
    ) -> Box<CandidateGeneration> {
        let prev;
        if scope_id < matrix.prefix.last_scope() {
            prev = Some(Self::init_abstraction_recursively(matrix, scope_id + 1));
        } else {
            prev = None;
        }
        let scope = &matrix.prefix.scopes[scope_id as usize];
        let result = Box::new(CandidateGeneration::new(
            matrix,
            scope,
            Quantifier::from(scope_id),
            prev,
        ));

        #[cfg(debug_assertions)]
        {
            // check consistency of interface literals
            // for every b_lit in abstraction, there is a corresponding t_lit in one of its inner abstractions
            for (clause_id, b_lit) in result.b_literals.iter() {
                let mut current = &result;
                let mut found = false;
                while let Some(next) = current.next.as_ref() {
                    if next.t_literals.contains_key(clause_id) {
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
            }

            if scope_id == 0 {
                let mut abstractions = Vec::new();
                Self::verify_t_literals(&mut abstractions, result.as_ref());
            }
        }

        result
    }

    #[cfg(debug_assertions)]
    fn verify_t_literals<'a>(
        abstractions: &mut Vec<&'a CandidateGeneration>,
        scope: &'a CandidateGeneration,
    ) {
        // check that for every clause containing a t-literal at this scope,
        // there is a clause containing a b-literal in the previous scope
        abstractions.push(scope);
        match scope.next.as_ref() {
            None => return,
            Some(next) => {
                debug!("{} {}", next.scope_id, abstractions.len());

                for (clause_id, t_lit) in next.t_literals.iter() {
                    let has_matching_b_lit =
                        abstractions.iter().fold(false, |val, &abstraction| {
                            val || abstraction.b_literals.contains_key(clause_id)
                        });
                    if !has_matching_b_lit {
                        panic!(
                            "missing b-literal for t-literal {} at scope {}",
                            clause_id, next.scope_id
                        );
                    }
                }

                Self::verify_t_literals(abstractions, next);
            }
        }
        abstractions.pop();
    }

    fn new_existential(&mut self, matrix: &QMatrix, scope: &Scope) {
        // build SAT instance for existential quantifier: abstract all literals that are not contained in quantifier into b- and t-literals
        for (clause_id, clause) in matrix.clauses.iter().enumerate() {
            debug_assert!(clause.len() != 0, "unit clauses indicate a problem");

            let mut contains_variables = false;

            let mut sat_clause = Vec::new();
            let mut scopes = MinMax::new();

            for &literal in clause.iter() {
                let var_scope = matrix.prefix.get(literal.variable()).scope;
                scopes.update(var_scope);
                if var_scope != scope.id {
                    continue;
                }
                contains_variables = true;
                sat_clause.push(self.lit_to_sat_lit(literal));
            }

            // add t- and b-lits to existential quantifiers:
            // * we add t-lit if scope is between min- and max-scope of current clause
            // * we add b-lit if scope is between min- and max-scope of current clause, excluding max-scope
            let (min_scope, max_scope) = scopes.get();
            let need_t_lit = contains_variables && min_scope < scope.id && scope.id <= max_scope;
            let need_b_lit = contains_variables && min_scope <= scope.id && scope.id < max_scope;

            if !contains_variables {
                debug_assert!(!need_t_lit);
                debug_assert!(!need_b_lit);
                debug_assert!(sat_clause.is_empty());
                continue;
            }

            if need_t_lit {
                let t_lit = self.sat.new_var();
                sat_clause.push(t_lit);
                self.t_literals.insert(clause_id as ClauseId, t_lit);
                self.reverse_t_literals
                    .insert(t_lit.var(), clause_id as ClauseId);
            }

            if need_b_lit {
                let b_lit = self.sat.new_var();
                sat_clause.push(!b_lit);
                self.b_literals.insert(clause_id as ClauseId, b_lit);
            }

            debug_assert!(!sat_clause.is_empty());
            self.sat.add_clause(sat_clause.as_ref());
        }

        debug!("Scope {}", scope.id);
        debug!("t-literals: {}", self.t_literals.len());
        debug!("b-literals: {}", self.b_literals.len());
    }

    fn new_universal(&mut self, matrix: &QMatrix, scope: &Scope) {
        // build SAT instance for negation of clauses, i.e., basically we only build binary clauses
        for (clause_id, clause) in matrix.clauses.iter().enumerate() {
            debug_assert!(clause.len() != 0, "unit clauses indicate a problem");

            let mut scopes = MinMax::new();

            let mut sat_var = None;
            for &literal in clause.iter() {
                let var_scope = matrix.prefix.get(literal.variable()).scope;
                scopes.update(var_scope);
                if var_scope != scope.id {
                    continue;
                }
                if sat_var == None {
                    sat_var = Some(self.sat.new_var());
                }
                let lit = self.lit_to_sat_lit(literal);
                self.sat.add_clause(&[!sat_var.unwrap(), !lit]);
            }
            if sat_var == None {
                // no variable of current scope
                continue;
            }
            let sat_var = sat_var.unwrap();

            let (min_scope, max_scope) = scopes.get();
            let need_t_lit = min_scope < scope.id && scope.id <= max_scope;
            let need_b_lit = min_scope <= scope.id && scope.id <= max_scope;

            if need_t_lit {
                self.t_literals.insert(clause_id as ClauseId, sat_var);
                self.reverse_t_literals
                    .insert(sat_var.var(), clause_id as ClauseId);
            }

            if need_b_lit {
                self.b_literals.insert(clause_id as ClauseId, sat_var);
            }
        }

        println!("Scope {}", scope.id);
        println!("t-literals: {}", self.t_literals.len());
        println!("b-literals: {}", self.b_literals.len());
    }

    fn lit_to_sat_lit(&self, literal: Literal) -> Lit {
        let lit = self.variable_to_sat[&literal.variable()];
        if literal.signed() {
            !lit
        } else {
            lit
        }
    }

    fn solve_recursive(&mut self, matrix: &QMatrix) -> SolverResult {
        trace!("solve_recursive");

        let good_result = if self.is_universal {
            SolverResult::Unsatisfiable
        } else {
            SolverResult::Satisfiable
        };
        let bad_result = if self.is_universal {
            SolverResult::Satisfiable
        } else {
            SolverResult::Unsatisfiable
        };
        debug_assert!(good_result != bad_result);

        loop {
            debug!("");
            debug!("solve level {}", self.scope_id);

            match self.check_candidate_exists() {
                Lbool::True => {
                    // there is a candidate solution, verify it recursively
                    self.update_assignment();
                    if self.next.is_none() {
                        // innermost scope, propagate result to outer scopes
                        self.min_entry.clone_from(&self.entry);
                        debug_assert!(!self.is_universal);
                        // TODO: optimize min_entry
                        return good_result;
                    }

                    self.get_assumptions(matrix);

                    let result = self.next.as_mut().unwrap().solve_recursive(matrix);

                    if result == good_result {
                        // TODO: do entry optimization
                        self.min_entry
                            .clone_from(&self.next.as_ref().unwrap().min_entry);
                        return good_result;
                    } else {
                        debug_assert!(result == bad_result);

                        self.refine();
                        continue;
                    }
                }
                Lbool::False => {
                    // there is no candidate solution, return witness
                    self.get_unsat_core();
                    return bad_result;
                }
                _ => panic!("inconsistent internal state"),
            }
        }
    }

    fn check_candidate_exists(&mut self) -> Lbool {
        self.sat_solver_assumptions.clear();

        let mut assumptions = Vec::new();

        let mut debug_print = String::new();

        for (&clause_id, &t_literal) in self.t_literals.iter() {
            let mut t_literal = t_literal;
            if !self.entry[clause_id as usize] {
                t_literal = !t_literal;
            }
            if self.is_universal {
                t_literal = !t_literal;
            }

            if t_literal.isneg() {
                debug_print.push_str(&format!(" t{}", clause_id));
            } else {
                debug_print.push_str(&format!(" -t{}", clause_id));
            }

            if self.is_universal && !t_literal.isneg() {
                // assume t-literal completely for existential quantifier
                // and only negatively for universal quantifier
                continue;
            }

            assumptions.push(t_literal);

            if t_literal.isneg() {
                self.sat_solver_assumptions.push(clause_id);
            }
        }
        debug!("assume {}", debug_print);
        self.sat.solve_with_assumptions(assumptions.as_ref())
    }

    fn update_assignment(&mut self) {
        trace!("update_assignment");

        let mut debug_print = String::new();

        let model = self.sat.get_model();
        for (&variable, &sat_var) in self.variable_to_sat.iter() {
            let value = match model[sat_var.var() as usize] {
                Lbool::True => true,
                Lbool::False => false,
                _ => panic!("expect all variables to be assigned"),
            };
            if value {
                debug_print.push_str(&format!(" {}", variable));
            } else {
                debug_print.push_str(&format!(" -{}", variable));
            }
            let old = self.assignments.entry(variable).or_insert(value);
            *old = value;
        }
        debug!("assignment {}", debug_print);
    }

    fn get_assumptions(&mut self, matrix: &QMatrix) {
        trace!("get_assumptions");

        let assumptions = &mut self.next.as_mut().unwrap().entry;

        let len = assumptions.len();
        assumptions.clear();
        assumptions.resize(len, false);

        let mut debug_print = String::new();

        let model = self.sat.get_model();
        if !self.is_universal {
            for (&clause_id, b_lit) in self.b_literals.iter() {
                let value = model[b_lit.var() as usize];
                if value != Lbool::False {
                    assumptions[clause_id as usize] = true;
                    continue;
                }
                debug_assert!(
                    !self.entry[clause_id as usize] || assumptions[clause_id as usize],
                    "entry -> assumption"
                );

                debug_assert!(
                    !self.entry[clause_id as usize],
                    "may be true, would reduce overhead, so early return"
                );

                // assumption literal was set, but it may be still true that the clause is satisfied
                let clause = &matrix.clauses[clause_id as usize];
                let mut is_satisfied = false;
                for literal in clause.iter() {
                    if !self.variable_to_sat.contains_key(&literal.variable()) {
                        // not a variable of current level
                        continue;
                    }
                    let value = self.assignments[&literal.variable()];
                    if value && !literal.signed() {
                        is_satisfied = true;
                        break;
                    } else if !value && literal.signed() {
                        is_satisfied = true;
                        break;
                    }
                }
                if is_satisfied {
                    assumptions[clause_id as usize] = true;
                    continue;
                }

                debug_print.push_str(&format!(" b{}", clause_id));
            }
        } else {
            for (&clause_id, b_lit) in self.b_literals.iter() {
                let value = model[b_lit.var() as usize];
                if value != Lbool::False {
                    continue;
                }

                // assumption literal was set
                // check if clause is falsified by current level
                let clause = &matrix.clauses[clause_id as usize];
                let mut falsified = true;
                let mut nonempty = false;

                for literal in clause.iter() {
                    if !self.variable_to_sat.contains_key(&literal.variable()) {
                        // not a variable of current level
                        continue;
                    }
                    nonempty = true;
                    let value = self.assignments[&literal.variable()];
                    if value && !literal.signed() {
                        falsified = false;
                        break;
                    } else if !value && literal.signed() {
                        falsified = false;
                        break;
                    }
                }
                if nonempty && falsified {
                    if self.t_literals.contains_key(&clause_id) {
                        if !self.entry[clause_id as usize] {
                            continue;
                        }
                    } else {
                        continue;
                    }
                }
                if !nonempty {
                    debug_assert!(self.t_literals.contains_key(&clause_id));
                    if !self.entry[clause_id as usize] {
                        continue;
                    }
                }

                assumptions[clause_id as usize] = true;

                debug_print.push_str(&format!(" b{}", clause_id));
            }
        }
        debug!("assumptions: {}", debug_print);
    }

    fn refine(&mut self) {
        trace!("refine");
        let entry = &self.next.as_ref().unwrap().min_entry;
        let mut sat_clause = Vec::new();

        let mut debug_print = String::new();

        for (i, val) in entry.iter().enumerate() {
            if !val {
                continue;
            }
            let clause_id = i as ClauseId;
            let b_lit = self.b_literals[&clause_id];
            sat_clause.push(b_lit);
            debug_print.push_str(&format!(" b{}", clause_id));
        }
        self.sat.add_clause(sat_clause.as_ref());
        debug!("refinement: {}", debug_print);
    }

    fn get_unsat_core(&mut self) {
        trace!("unsat_core");

        let len = self.entry.len();
        self.entry.clear();
        self.entry.resize(len, false);

        let mut debug_print = String::new();

        let failed = self.sat.get_conflict();
        for l in failed {
            let clause_id = self.reverse_t_literals[&l.var()];
            self.entry[clause_id as usize] = true;
            debug_print.push_str(&format!(" t{}", clause_id));
        }
        debug!("unsat core: {}", debug_print);
    }
}

struct MinMax {
    min: Option<i32>,
    max: Option<i32>,
}

impl MinMax {
    fn new() -> MinMax {
        MinMax {
            min: None,
            max: None,
        }
    }

    fn update(&mut self, value: i32) {
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

    fn min(&self) -> i32 {
        self.min.unwrap()
    }

    fn max(&self) -> i32 {
        self.max.unwrap()
    }

    fn get(&self) -> (i32, i32) {
        (self.min(), self.max())
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use solver::Solver;

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
        let matrix = qdimacs::parse(&instance).unwrap();
        let mut solver = CaqeSolver::new(&matrix);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
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
        let matrix = qdimacs::parse(&instance).unwrap();
        let mut solver = CaqeSolver::new(&matrix);
        assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
    }
}
