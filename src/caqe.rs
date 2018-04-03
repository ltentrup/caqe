extern crate cryptominisat;
use self::cryptominisat::*;

use super::*;

use std::collections::HashMap;

type QMatrix = Matrix<HierarchicalPrefix>;

pub struct CaqeSolver<'a> {
    matrix: &'a QMatrix,
    abstraction: Box<ScopeRecursiveSolver>,
}

impl<'a> CaqeSolver<'a> {
    pub fn new(matrix: &'a QMatrix) -> CaqeSolver {
        debug_assert!(!matrix.conflict());
        CaqeSolver {
            matrix: matrix,
            abstraction: ScopeRecursiveSolver::init_abstraction_recursively(matrix, 0),
        }
    }
}

impl<'a> super::Solver for CaqeSolver<'a> {
    fn solve(&mut self) -> SolverResult {
        self.abstraction.as_mut().solve_recursive(self.matrix)
    }
}

struct ScopeSolverData {
    sat: cryptominisat::Solver,
    variable_to_sat: HashMap<Variable, Lit>,
    t_literals: HashMap<ClauseId, Lit>,
    b_literals: HashMap<ClauseId, Lit>,

    /// lookup from sat solver variables to clause id's
    reverse_t_literals: HashMap<u32, ClauseId>,

    assignments: HashMap<Variable, bool>,

    /// stores for every clause whether the clause is satisfied or not by assignments to outer variables
    entry: Vec<bool>,

    /// stores the assumptions (as clause id's) given to sat solver
    sat_solver_assumptions: Vec<ClauseId>,

    is_universal: bool,
    scope_id: ScopeId,
}

impl ScopeSolverData {
    fn new(matrix: &QMatrix, scope: &Scope) -> ScopeSolverData {
        let mut entry = Vec::new();
        entry.resize(matrix.clauses.len(), false);
        ScopeSolverData {
            sat: cryptominisat::Solver::new(),
            variable_to_sat: HashMap::new(),
            t_literals: HashMap::new(),
            b_literals: HashMap::new(),
            reverse_t_literals: HashMap::new(),
            assignments: HashMap::new(),
            entry: entry,
            sat_solver_assumptions: Vec::new(),
            is_universal: scope.id % 2 != 0,
            scope_id: scope.id,
        }
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

        #[cfg(debug_assertions)]
        {
            let mut t_literals = String::new();
            for clause_id in self.t_literals.keys() {
                t_literals.push_str(&format!(" t{}", clause_id));
            }
            debug!("t-literals: {}", t_literals);

            let mut b_literals = String::new();
            for clause_id in self.b_literals.keys() {
                b_literals.push_str(&format!(" b{}", clause_id));
            }
            debug!("b-literals: {}", b_literals);
        }
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

        debug!("Scope {}", scope.id);
        debug!("t-literals: {}", self.t_literals.len());
        debug!("b-literals: {}", self.b_literals.len());

        #[cfg(debug_assertions)]
        {
            let mut t_literals = String::new();
            for clause_id in self.t_literals.keys() {
                t_literals.push_str(&format!(" t{}", clause_id));
            }
            debug!("t-literals: {}", t_literals);

            let mut b_literals = String::new();
            for clause_id in self.b_literals.keys() {
                b_literals.push_str(&format!(" b{}", clause_id));
            }
            debug!("b-literals: {}", b_literals);
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

    fn check_candidate_exists(&mut self, next: &mut Option<Box<ScopeRecursiveSolver>>) -> Lbool {
        // we need to reset abstraction entries for next scopes, since some entries may be pushed down
        if next.is_some() {
            next.as_mut().unwrap().data.entry.clone_from(&self.entry);
        }

        self.sat_solver_assumptions.clear();

        let mut assumptions = Vec::new();

        #[cfg(debug_assertions)]
        let mut debug_print = String::new();

        // we iterate in parallel over the entry and the t-literals of current level
        // there are 3 possibilities:
        // * clause from entry is not a t-lit: push entry to next quantifier
        // * clause is in entry and a t-lit: assume positively
        // * clause is not in entry and a t-lit: assume negatively
        for (&clause_id, &t_literal) in self.t_literals.iter() {
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

            assumptions.push(t_literal);

            if t_literal.isneg() {
                self.sat_solver_assumptions.push(clause_id);
            }
        }

        #[cfg(debug_assertions)]
        debug!("assume {}", debug_print);

        self.sat.solve_with_assumptions(assumptions.as_ref())
    }

    fn update_assignment(&mut self) {
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

            let old = self.assignments.entry(variable).or_insert(value);
            *old = value;
        }

        #[cfg(debug_assertions)]
        debug!("assignment {}", debug_print);
    }

    fn get_assumptions(&mut self, matrix: &QMatrix, next: &mut Box<ScopeRecursiveSolver>) {
        trace!("get_assumptions");

        // assumptions were already cleared in check_candidate_exists
        let assumptions = &mut next.data.entry;

        #[cfg(debug_assertions)]
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

                if self.entry[clause_id as usize] {
                    debug_assert!(assumptions[clause_id as usize]);
                    continue;
                }

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

                #[cfg(debug_assertions)]
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

                #[cfg(debug_assertions)]
                debug_print.push_str(&format!(" b{}", clause_id));
            }
        }

        #[cfg(debug_assertions)]
        debug!("assumptions: {}", debug_print);
    }

    fn entry_minimization(
        &mut self,
        matrix: &QMatrix,
        next: Option<&mut Box<ScopeRecursiveSolver>>,
    ) {
        trace!("entry_minimization");

        if next.is_some() {
            // we have to set the t-literals for which there are no corresponding b-literals
            // TODO: current refinement literals
        }

        for (&variable, value) in self.assignments.iter() {
            let literal = Literal::new(variable, !value);

            // check if assignment is needed, i.e., it can flip a bit in entry
            let mut needed = false;
            for &clause_id in matrix.occurrences(literal) {
                if self.entry[clause_id as usize] {
                    needed = true;
                    self.entry[clause_id as usize] = false;
                }
            }

            // TODO: check the case for self.next.is_none()
            if !needed && next.is_some() {
                // the current value set is not needed for the entry, try other polarity
                for &clause_id in matrix.occurrences(-literal) {
                    if self.entry[clause_id as usize] {
                        self.entry[clause_id as usize] = false;
                    }
                }
            }
        }
    }

    fn refine(&mut self, next: &mut Box<ScopeRecursiveSolver>) {
        trace!("refine");
        let entry = &next.data.entry;
        let mut sat_clause = Vec::new();

        #[cfg(debug_assertions)]
        let mut debug_print = String::new();

        for (i, val) in entry.iter().enumerate() {
            if !val {
                continue;
            }
            let clause_id = i as ClauseId;
            let b_lit = self.add_b_lit_and_adapt_abstraction(clause_id);
            sat_clause.push(b_lit);

            #[cfg(debug_assertions)]
            debug_print.push_str(&format!(" b{}", clause_id));
        }
        self.sat.add_clause(sat_clause.as_ref());

        #[cfg(debug_assertions)]
        debug!("refinement: {}", debug_print);
    }

    fn add_b_lit_and_adapt_abstraction(&mut self, clause_id: ClauseId) -> Lit {
        let sat = &mut self.sat;
        let b_literals = &mut self.b_literals;
        let t_literals = &mut self.t_literals;
        let reverse_t_literals = &mut self.reverse_t_literals;
        let b_lit = b_literals.entry(clause_id).or_insert_with(|| {
            // A new b-literal has to be inserted
            // Create a new SAT solver literal and add it to both, t-literals and b-literals
            let b_lit = sat.new_var();
            t_literals.insert(clause_id, b_lit);
            reverse_t_literals.insert(b_lit.var(), clause_id);
            b_lit
        });
        *b_lit
    }

    fn get_unsat_core(&mut self) {
        trace!("unsat_core");

        let len = self.entry.len();
        self.entry.clear();
        self.entry.resize(len, false);

        #[cfg(debug_assertions)]
        let mut debug_print = String::new();

        let failed = self.sat.get_conflict();
        for l in failed {
            let clause_id = self.reverse_t_literals[&l.var()];
            self.entry[clause_id as usize] = true;

            #[cfg(debug_assertions)]
            debug_print.push_str(&format!(" t{}", clause_id));
        }

        #[cfg(debug_assertions)]
        debug!("unsat core: {}", debug_print);
    }

    fn unsat_propagation(&mut self, matrix: &QMatrix) {
        // TODO: can be optimized
        for (i, val) in self.entry.iter_mut().enumerate() {
            if *val == false {
                continue;
            }
            let min = matrix.clauses[i].iter().fold(
                matrix.prefix.last_scope(),
                |min_scope, literal| {
                    let var_scope = matrix.prefix.get(literal.variable()).scope;
                    if var_scope < min_scope {
                        var_scope
                    } else {
                        min_scope
                    }
                },
            );
            if min == self.scope_id {
                *val = false;
                continue;
            }
            debug_assert!(min < self.scope_id);
        }
    }
}

struct ScopeRecursiveSolver {
    data: ScopeSolverData,
    next: Option<Box<ScopeRecursiveSolver>>,
}

impl ScopeRecursiveSolver {
    fn new(
        matrix: &QMatrix,
        scope: &Scope,
        quantifier: Quantifier,
        next: Option<Box<ScopeRecursiveSolver>>,
    ) -> ScopeRecursiveSolver {
        let mut candidate = ScopeRecursiveSolver {
            data: ScopeSolverData::new(matrix, scope),
            next: next,
        };

        // add variables of scope to sat solver
        for &variable in scope.variables.iter() {
            candidate
                .data
                .variable_to_sat
                .insert(variable, candidate.data.sat.new_var());
        }

        match quantifier {
            Quantifier::Existential => candidate.data.new_existential(matrix, scope),
            Quantifier::Universal => candidate.data.new_universal(matrix, scope),
        }

        candidate
    }

    fn init_abstraction_recursively(
        matrix: &QMatrix,
        scope_id: ScopeId,
    ) -> Box<ScopeRecursiveSolver> {
        let prev;
        if scope_id < matrix.prefix.last_scope() {
            prev = Some(Self::init_abstraction_recursively(matrix, scope_id + 1));
        } else {
            prev = None;
        }
        let scope = &matrix.prefix.scopes[scope_id as usize];
        let result = Box::new(ScopeRecursiveSolver::new(
            matrix,
            scope,
            Quantifier::from(scope_id),
            prev,
        ));

        #[cfg(debug_assertions)]
        {
            // check consistency of interface literals
            // for every b_lit in abstraction, there is a corresponding t_lit in one of its inner abstractions
            for (clause_id, _b_lit) in result.data.b_literals.iter() {
                let mut current = &result;
                let mut found = false;
                while let Some(next) = current.next.as_ref() {
                    if next.data.t_literals.contains_key(clause_id) {
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
        abstractions: &mut Vec<&'a ScopeRecursiveSolver>,
        scope: &'a ScopeRecursiveSolver,
    ) {
        // check that for every clause containing a t-literal at this scope,
        // there is a clause containing a b-literal in the previous scope
        abstractions.push(scope);
        match scope.next.as_ref() {
            None => return,
            Some(next) => {
                for (clause_id, _t_lit) in next.data.t_literals.iter() {
                    let has_matching_b_lit =
                        abstractions.iter().fold(false, |val, &abstraction| {
                            val || abstraction.data.b_literals.contains_key(clause_id)
                        });
                    if !has_matching_b_lit {
                        panic!(
                            "missing b-literal for t-literal {} at scope {}",
                            clause_id, next.data.scope_id
                        );
                    }
                }

                Self::verify_t_literals(abstractions, next);
            }
        }
        abstractions.pop();
    }

    fn solve_recursive(&mut self, matrix: &QMatrix) -> SolverResult {
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
            debug!("solve level {}", current.scope_id);

            match current.check_candidate_exists(next) {
                Lbool::True => {
                    // there is a candidate solution, verify it recursively
                    current.update_assignment();

                    let next = match next {
                        &mut None => {
                            // innermost scope, propagate result to outer scopes
                            debug_assert!(!current.is_universal);
                            current.entry_minimization(matrix, None);
                            return good_result;
                        }
                        &mut Some(ref mut next) => next,
                    };

                    current.get_assumptions(matrix, next);

                    let result = next.solve_recursive(matrix);

                    if result == good_result {
                        current.entry.clone_from(&next.data.entry);
                        if current.is_universal {
                            current.unsat_propagation(matrix);
                        } else {
                            current.entry_minimization(matrix, Some(next));
                        }
                        return good_result;
                    } else {
                        debug_assert!(result == bad_result);

                        current.refine(next);
                        continue;
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
    fn test_false() {
        let instance = "p cnf 0 1\n0\n";
        let matrix = qdimacs::parse(&instance).unwrap();
        assert!(matrix.conflict());
    }

    #[test]
    fn test_true() {
        let instance = "p cnf 0 0";
        let matrix = qdimacs::parse(&instance).unwrap();
        let mut solver = CaqeSolver::new(&matrix);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
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
        let matrix = qdimacs::parse(&instance).unwrap();
        let mut solver = CaqeSolver::new(&matrix);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
    }
}
