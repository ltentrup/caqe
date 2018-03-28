extern crate cryptominisat;
use self::cryptominisat::*;

use super::*;

use std::collections::HashMap;

type ClauseId = u32;

type QMatrix = Matrix<HierarchicalPrefix>;

pub struct CaqeSolver<'a> {
    matrix: &'a QMatrix,
    abstractions: Vec<CandidateGeneration>,
    assignments: HashMap<Variable, bool>,
    min_entry: Vec<bool>,
}

impl<'a> CaqeSolver<'a> {
    pub fn new(matrix: &'a QMatrix) -> CaqeSolver {
        let mut abstractions = Vec::new();
        for (i, scope) in matrix.prefix.scopes.iter().enumerate() {
            println!("{:?}", scope);
            abstractions.push(CandidateGeneration::new(matrix, scope, Quantifier::from(i)));
        }
        let mut min_entry = Vec::new();
        min_entry.resize(matrix.clauses.len(), false);

        CaqeSolver {
            matrix: matrix,
            abstractions: abstractions,
            assignments: HashMap::new(),
            min_entry: min_entry,
        }
    }

    fn solve_scope(&mut self, scope_id: ScopeId) -> ScopeResult {
        // we need to borrow current scope and following scope
        // thus, the need to split the array
        let (head, tail) = self.abstractions.split_at_mut((scope_id + 1) as usize);
        let scope = &mut head[scope_id as usize];

        debug!("");
        debug!("solve level {}", scope_id);

        match scope.check_candidate_exists() {
            Lbool::True => {
                // there is a candidate solution, verify it recursively
                scope.update_assignment(&mut self.assignments);
                if scope_id == self.matrix.prefix.last_scope() {
                    // innermost scope, propagate result to outer scopes
                    self.min_entry.clone_from(&scope.entry);
                    return ScopeResult::CandidateVerified;
                }
                let assumptions = &mut tail[0].entry;
                scope.get_assumptions(self.matrix, &self.assignments, assumptions);
                return ScopeResult::CandidateFound;
            }
            Lbool::False => {
                // there is no candidate solution, return witness
                scope.get_unsat_core(&mut self.min_entry);
                return ScopeResult::CandidateRefuted;
            }
            _ => panic!("inconsistent internal state"),
        }
    }

    fn optimize_sat_entry(&mut self, current: ScopeId) -> Option<ScopeId> {
        assert!(Quantifier::from(current) == Quantifier::Existential);
        debug!("entry {:?}", self.min_entry);

        let mut current = current;
        let mut next = current - 1;
        loop {
            if current == 0 {
                // instance is satisfiable
                return None;
            }
            // TODO: add local refinement literals
            // TODO: optimize entry based on current scope (need occurrence list in matrix)
            // TODO: check if `next` scope influences entry
            let scope = &mut self.abstractions[next as usize];
            scope.refine(&self.min_entry);
            return Some(next);
        }
    }

    fn optimize_unsat_entry(&mut self, current: ScopeId) -> Option<ScopeId> {
        assert!(Quantifier::from(current) == Quantifier::Universal);
        debug!("entry {:?}", self.min_entry);
        let mut current = current;
        let mut next = current - 1;
        loop {
            if current == 1 {
                // instance is satisfiable
                return None;
            }
            let scope = &mut self.abstractions[next as usize];
            scope.refine(&self.min_entry);
            return Some(next);
        }
        None
    }
}

enum ScopeResult {
    CandidateFound,
    CandidateVerified,
    CandidateRefuted,
}

impl<'a> super::Solver for CaqeSolver<'a> {
    fn solve(&mut self) -> SolverResult {
        let initial_scope;
        if self.matrix.prefix.scopes[0].variables.is_empty() {
            // top-level existential scope is empty
            initial_scope = 1;
        } else {
            initial_scope = 0;
        }

        let mut current_scope = initial_scope;
        loop {
            match self.solve_scope(current_scope) {
                ScopeResult::CandidateFound => {
                    current_scope += 1;
                }
                ScopeResult::CandidateVerified => {
                    assert!(current_scope == self.matrix.prefix.last_scope());
                    match self.optimize_sat_entry(current_scope) {
                        None => return SolverResult::Satisfiable,
                        Some(next) => current_scope = next,
                    }
                }
                ScopeResult::CandidateRefuted => match Quantifier::from(current_scope) {
                    Quantifier::Existential => match self.optimize_unsat_entry(current_scope - 1) {
                        None => return SolverResult::Unsatisfiable,
                        Some(next) => current_scope = next,
                    },
                    Quantifier::Universal => match self.optimize_sat_entry(current_scope - 1) {
                        None => return SolverResult::Satisfiable,
                        Some(next) => current_scope = next,
                    },
                },
            }
        }
        SolverResult::Unknown
    }
}

struct CandidateGeneration {
    sat: cryptominisat::Solver,
    variable_to_sat: HashMap<Variable, Lit>,
    t_literals: HashMap<ClauseId, Lit>,
    b_literals: HashMap<ClauseId, Lit>,

    /// lookup from sat solver variables to clause id's
    reverse_t_literals: HashMap<u32, ClauseId>,

    /// stores for every clause whether the clause is satisfied or not by assignments to outer variables
    entry: Vec<bool>,

    /// stores the assumptions (as clause id's) given to sat solver
    sat_solver_assumptions: Vec<ClauseId>,

    is_universal: bool,
}

impl CandidateGeneration {
    fn new(matrix: &QMatrix, scope: &Scope, quantifier: Quantifier) -> CandidateGeneration {
        let mut entry = Vec::new();
        entry.resize(matrix.clauses.len(), false);
        let mut candidate = CandidateGeneration {
            sat: cryptominisat::Solver::new(),
            variable_to_sat: HashMap::new(),
            t_literals: HashMap::new(),
            b_literals: HashMap::new(),
            reverse_t_literals: HashMap::new(),
            entry: entry,
            sat_solver_assumptions: Vec::new(),
            is_universal: scope.id % 2 != 0,
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

    fn new_existential(&mut self, matrix: &QMatrix, scope: &Scope) {
        // build SAT instance for existential quantifier: abstract all literals that are not contained in quantifier into b- and t-literals
        for (clause_id, clause) in matrix.clauses.iter().enumerate() {
            assert!(clause.len() != 0, "unit clauses indicate a problem");

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
                assert!(!need_t_lit);
                assert!(!need_b_lit);
                assert!(sat_clause.is_empty());
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

            assert!(!sat_clause.is_empty());
            self.sat.add_clause(sat_clause.as_ref());
        }

        println!("Scope {}", scope.id);
        println!("t-literals: {}", self.t_literals.len());
        println!("b-literals: {}", self.b_literals.len());
    }

    fn new_universal(&mut self, matrix: &QMatrix, scope: &Scope) {
        // build SAT instance for negation of clauses, i.e., basically we only build binary clauses
        for (clause_id, clause) in matrix.clauses.iter().enumerate() {
            assert!(clause.len() != 0, "unit clauses indicate a problem");

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

    fn check_candidate_exists(&mut self) -> Lbool {
        self.sat_solver_assumptions.clear();

        let mut assumptions = Vec::new();

        for (&clause_id, &t_literal) in self.t_literals.iter() {
            let mut t_literal = t_literal;
            if !self.entry[clause_id as usize] {
                t_literal = !t_literal;
            }
            if self.is_universal {
                t_literal = !t_literal;
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
        self.sat.solve_with_assumptions(assumptions.as_ref())
    }

    fn update_assignment(&mut self, assignment: &mut HashMap<Variable, bool>) {
        trace!("update_assignment");
        let model = self.sat.get_model();
        for (&variable, &sat_var) in self.variable_to_sat.iter() {
            let value = match model[sat_var.var() as usize] {
                Lbool::True => true,
                Lbool::False => false,
                _ => panic!("expect all variables to be assigned"),
            };
            debug!("variable {} {}", variable, value);
            let old = assignment.entry(variable).or_insert(value);
            *old = value;
        }
        debug!("assignment {:?}", assignment);
    }

    fn get_assumptions(
        &mut self,
        matrix: &QMatrix,
        assignment: &HashMap<Variable, bool>,
        assumptions: &mut Vec<bool>,
    ) {
        trace!("get_assumptions");
        let len = assumptions.len();
        assumptions.clear();
        assumptions.resize(len, false);

        let model = self.sat.get_model();
        if !self.is_universal {
            for (&clause_id, b_lit) in self.b_literals.iter() {
                let value = model[b_lit.var() as usize];
                if value != Lbool::False {
                    assumptions[clause_id as usize] = true;
                    continue;
                }
                assert!(
                    !self.entry[clause_id as usize] || assumptions[clause_id as usize],
                    "entry -> assumption"
                );

                assert!(
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
                    let value = assignment[&literal.variable()];
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
                    let value = assignment[&literal.variable()];
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
                    assert!(self.t_literals.contains_key(&clause_id));
                    if !self.entry[clause_id as usize] {
                        continue;
                    }
                }

                assumptions[clause_id as usize] = true;
            }
        }
        debug!("assumptions: {:?}", assumptions);
    }

    fn refine(&mut self, entry: &Vec<bool>) {
        trace!("refine");
        let mut sat_clause = Vec::new();
        for (i, val) in entry.iter().enumerate() {
            if !val {
                continue;
            }
            let clause_id = i as ClauseId;
            let b_lit = self.b_literals[&clause_id];
            sat_clause.push(b_lit);
            debug!("b{}", clause_id);
        }
        self.sat.add_clause(sat_clause.as_ref());
    }

    fn get_unsat_core(&mut self, entry: &mut Vec<bool>) {
        trace!("unsat_core");

        let len = entry.len();
        entry.clear();
        entry.resize(len, false);

        let failed = self.sat.get_conflict();
        for l in failed {
            let clause_id = self.reverse_t_literals[&l.var()];
            entry[clause_id as usize] = true;
        }
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
