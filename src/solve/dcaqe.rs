extern crate cryptominisat;
use self::cryptominisat::*;

extern crate bit_vec;
use self::bit_vec::BitVec;

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
        let mut global = GlobalSolverData::new();

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
            println!("{:?} {:?}", universals, antichain);

            if !universals.is_empty() {
                let level = abstractions.len();
                for &var in &universals {
                    global.level_lookup.insert(var, level);
                }
                abstractions.push(SolverLevel::Universal(Abstraction::new_universal(
                    matrix,
                    &universals,
                    &global.level_lookup,
                )));
            }
            let level = abstractions.len();
            abstractions.push(SolverLevel::Existential(
                antichain
                    .iter()
                    .map(|&scope_id| {
                        let scope = &matrix.prefix.scopes[scope_id];
                        for &var in &scope.existentials {
                            global.level_lookup.insert(var, level);
                        }
                        Abstraction::new_existential(matrix, scope)
                    })
                    .collect(),
            ))
        }
        (abstractions, global)
    }
}

impl<'a> super::Solver for DCaqeSolver<'a> {
    fn solve(&mut self) -> SolverResult {
        let mut level = 0;
        loop {
            match self.levels[level].solve_level(&mut self.matrix, &mut self.global) {
                SolveLevelResult::NextLevel(next) => {
                    panic!("todo: refinement");
                    level = next;
                }
                SolveLevelResult::SolverResult(res) => return res,
            }
        }
    }
}

enum SolverLevel {
    Universal(Abstraction),
    Existential(Vec<Abstraction>),
}

enum SolveLevelResult {
    NextLevel(usize),
    SolverResult(SolverResult),
}

impl SolverLevel {
    fn solve_level(
        &mut self,
        matrix: &mut DQMatrix,
        global: &mut GlobalSolverData,
    ) -> SolveLevelResult {
        match self {
            SolverLevel::Universal(abstraction) => match abstraction.solve(global) {
                AbstractionResult::CandidateFound => {
                    panic!("not implemented");
                }
                AbstractionResult::CandidateRefuted => {
                    panic!("not implemented");
                }
            },
            SolverLevel::Existential(abstractions) => {
                for abstraction in abstractions {
                    if abstraction.solve(global) == AbstractionResult::CandidateRefuted {
                        panic!("not implemented");
                    }
                }
                // all results were positive
                panic!("not implemented");
            }
        }
    }
}

struct GlobalSolverData {
    /// the current assignment
    assignments: FxHashMap<Variable, bool>,

    /// an mapping from variables to the level they are bound
    level_lookup: FxHashMap<Variable, usize>,
}

impl GlobalSolverData {
    fn new() -> GlobalSolverData {
        GlobalSolverData {
            assignments: FxHashMap::default(),
            level_lookup: FxHashMap::default(),
        }
    }
}

type AbstractionId = usize;

#[derive(Debug, PartialEq, Eq)]
enum AbstractionResult {
    CandidateFound,
    CandidateRefuted,
}

struct Abstraction {
    sat: cryptominisat::Solver,
    variable_to_sat: FxHashMap<Variable, Lit>,
    t_literals: Vec<(ClauseId, Lit)>,
    b_literals: Vec<(ClauseId, Lit)>,

    /// lookup from sat solver variables to clause id's
    reverse_t_literals: FxHashMap<u32, ClauseId>,
}

impl Abstraction {
    fn new() -> Abstraction {
        let mut sat = cryptominisat::Solver::new();
        sat.set_num_threads(1);
        Abstraction {
            sat,
            variable_to_sat: FxHashMap::default(),
            b_literals: Vec::new(),
            t_literals: Vec::new(),
            reverse_t_literals: FxHashMap::default(),
        }
    }

    fn new_universal(
        matrix: &DQMatrix,
        variables: &FxHashSet<Variable>,
        level_lookup: &FxHashMap<Variable, usize>,
    ) -> Abstraction {
        // build SAT instance for negation of clauses, i.e., basically we only build binary clauses
        debug_assert!(!variables.is_empty());

        let mut abs = Self::new();

        // add variables of scope to sat solver
        for &variable in variables {
            abs.variable_to_sat.insert(variable, abs.sat.new_var());
        }

        let mut need_b_lit = false;
        let mut need_t_lit = false;

        for (clause_id, clause) in matrix.clauses.iter().enumerate() {
            debug_assert!(clause.len() != 0, "unit clauses indicate a problem");

            let clause_id = clause_id as ClauseId;

            let mut sat_var = None;
            for &literal in clause.iter() {
                if !abs.variable_to_sat.contains_key(&literal.variable()) {
                    if level_lookup.contains_key(&literal.variable()) {
                        // bound outer, otherwise would not contained in level_lookup yet
                        need_t_lit = true;
                    }
                    continue;
                }
                let sat_var = *sat_var.get_or_insert_with(|| abs.sat.new_var());
                let lit = abs.lit_to_sat_lit(literal);
                abs.sat.add_clause(&[!sat_var, !lit]);
                need_b_lit = true;
            }

            if !need_b_lit {
                // no variable of current scope
                continue;
            }

            let sat_var = sat_var.expect("sat_var cannot be empty at this point");

            if need_t_lit {
                abs.t_literals.push((clause_id, sat_var));
                debug_assert!(!abs.reverse_t_literals.contains_key(&sat_var.var()));
                abs.reverse_t_literals.insert(sat_var.var(), clause_id);
            }

            if need_b_lit {
                abs.b_literals.push((clause_id, sat_var));
            }
        }

        abs
    }

    fn new_existential(matrix: &DQMatrix, scope: &Scope) -> Abstraction {
        let mut abs = Self::new();
        let mut sat_clause = Vec::new();

        // add variables of scope to sat solver
        for &variable in scope.existentials.iter() {
            abs.variable_to_sat.insert(variable, abs.sat.new_var());
        }

        for (clause_id, clause) in matrix.clauses.iter().enumerate() {
            debug_assert!(clause.len() != 0, "unit clauses indicate a problem");
            debug_assert!(sat_clause.is_empty());

            let mut need_b_lit = false;
            let mut need_t_lit = false;
            let mut contains_variables = false;

            for &literal in clause.iter() {
                if !abs.variable_to_sat.contains_key(&literal.variable()) {
                    // not of current scope
                    if matrix.prefix.depends_on_scope(scope, literal.variable()) {
                        // outer variable
                        need_t_lit = true;
                    } else {
                        // inner variable
                        need_b_lit = true;
                    }
                    continue;
                }
                contains_variables = true;
                sat_clause.push(abs.lit_to_sat_lit(literal));
            }

            if !contains_variables {
                debug_assert!(sat_clause.is_empty());
                continue;
            }

            if need_t_lit {
                let t_lit = abs.sat.new_var();
                sat_clause.push(t_lit);
                abs.t_literals.push((clause_id as ClauseId, t_lit));
                abs.reverse_t_literals
                    .insert(t_lit.var(), clause_id as ClauseId);
            }

            if need_b_lit {
                let b_lit = abs.sat.new_var();
                sat_clause.push(!b_lit);
                abs.b_literals.push((clause_id as ClauseId, b_lit));
            }

            debug_assert!(!sat_clause.is_empty());
            abs.sat.add_clause(sat_clause.as_ref());
            sat_clause.clear();
        }

        abs
    }

    fn lit_to_sat_lit(&self, literal: Literal) -> Lit {
        let lit = self.variable_to_sat[&literal.variable()];
        if literal.signed() {
            !lit
        } else {
            lit
        }
    }

    fn solve(&mut self, global: &mut GlobalSolverData) -> AbstractionResult {
        panic!("not implementde");
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use solve::Solver;

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
}
