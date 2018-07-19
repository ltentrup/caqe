// extern crates
#[macro_use]
extern crate log;
extern crate bit_vec;
extern crate clap;
extern crate rustc_hash;
extern crate simplelog;
extern crate tempfile;
#[macro_use]
extern crate uncover;

// This defines two macros, `covers!` and `covered_by!`.
// They will be no-ops unless `cfg!(debug_assertions)` is true.
define_uncover_macros!(enable_if(cfg!(debug_assertions)));

use bit_vec::BitVec;
use clap::{App, Arg};
use rustc_hash::{FxHashMap, FxHashSet};
use simplelog::*;
use tempfile::tempfile;

// Rust stdlib
use std::error::Error;
use std::fs::File;
use std::io::Read;
use std::str::FromStr;

// modules
mod literal;
pub use self::literal::Literal;
use literal::*; // re-export literals

mod clause;
use clause::*;

mod matrix;
pub use self::matrix::Matrix;
use matrix::*;

mod dimacs;
pub use dimacs::*;

mod preprocessor;
use preprocessor::*;

pub mod parse;
mod utils;

pub mod solve;
pub use solve::caqe::{CaqeSolver, CaqeSolverOptions};
pub use solve::dcaqe::DCaqeSolver;
pub use solve::{Solver, SolverResult};

#[cfg(feature = "statistics")]
use utils::statistics::TimingStats;

// Command line parsing

pub type CaqeConfig = CommonSolverConfig<CaqeSpecificSolverConfig>;
pub type DCaqeConfig = CommonSolverConfig<DCaqeSpecificSolverConfig>;

pub trait SolverSpecificConfig {
    fn add_arguments<'a, 'b>(app: App<'a, 'b>) -> App<'a, 'b>;
    fn parse_arguments(matches: &clap::ArgMatches) -> Self;
    const NAME: &'static str;
    const DESC: &'static str;
}

#[derive(Debug)]
pub struct CommonSolverConfig<T: SolverSpecificConfig> {
    /// None for stdin
    filename: Option<String>,
    verbosity: LevelFilter,
    statistics: bool,
    specific: T,
}

impl<T: SolverSpecificConfig> CommonSolverConfig<T> {
    pub fn new(args: &[String]) -> Self {
        let mut flags = App::new(T::NAME)
            .version(env!("CARGO_PKG_VERSION"))
            .author(env!("CARGO_PKG_AUTHORS"))
            .about(T::DESC)
            .arg(
                Arg::with_name("INPUT")
                    .help("Sets the input file to use")
                    .required(false)
                    .index(1),
            );
        #[cfg(debug_assertions)]
        {
            flags = flags.arg(
                Arg::with_name("v")
                    .short("v")
                    .multiple(true)
                    .help("Sets the level of verbosity"),
            );
        }
        #[cfg(feature = "statistics")]
        {
            flags = flags.arg(
                Arg::with_name("statistics")
                    .long("--statistics")
                    .help("Enables collection and printing of solving statistics"),
            )
        }
        flags = T::add_arguments(flags);

        let matches = flags.get_matches_from(args);

        let filename = matches.value_of("INPUT").map(|s| s.to_string());

        let verbosity = match matches.occurrences_of("v") {
            0 => LevelFilter::Warn,
            1 => LevelFilter::Info,
            2 => LevelFilter::Debug,
            3 | _ => LevelFilter::Trace,
        };

        let statistics = matches.is_present("statistics");

        CommonSolverConfig {
            filename,
            verbosity,
            statistics,
            specific: T::parse_arguments(&matches),
        }
    }
}

#[derive(Debug)]
pub struct CaqeSpecificSolverConfig {
    pub options: CaqeSolverOptions,
    pub qdimacs_output: bool,
    pub preprocessor: Option<QBFPreprocessor>,
}

impl SolverSpecificConfig for CaqeSpecificSolverConfig {
    const NAME: &'static str = "CAQE";
    const DESC: &'static str =
        "CAQE is a solver for quantified Boolean formulas (QBF) in QDIMACS format.";

    fn add_arguments<'a, 'b>(app: App<'a, 'b>) -> App<'a, 'b> {
        let default_options = CaqeSolverOptions::new();

        let default = |val| match val {
            true => "1",
            false => "0",
        };
        app.arg(
            Arg::with_name("preprocessor")
                .help("Sets the preprocessor to use")
                .long("--preprocessor")
                .takes_value(true)
                .requires("INPUT")
                .possible_values(QBFPreprocessor::values()),
        ).arg(
                Arg::with_name("qdimacs-output")
                    .long("--qdo")
                    .help("Prints QDIMACS output (partial assignment) after solving"),
            ).arg(
                Arg::with_name("strong-unsat-refinement")
                    .long("--strong-unsat-refinement")
                    .default_value(default(default_options.strong_unsat_refinement))
                    .value_name("bool")
                    .takes_value(true)
                    .possible_values(&["0", "1"])
                    .hide_possible_values(true)
                    .help("Controls whether strong unsat refinement should be used"),
            ).arg(
                Arg::with_name("expansion-refinement")
                    .long("--expansion-refinement")
                    .default_value(default(default_options.expansion_refinement))
                    .value_name("bool")
                    .takes_value(true)
                    .possible_values(&["0", "1"])
                    .hide_possible_values(true)
                    .help("Controls whether expansion refinement should be used"),
            ).arg(
                Arg::with_name("refinement-literal-subsumption")
                    .long("--refinement-literal-subsumption")
                    .default_value(default(default_options.refinement_literal_subsumption))
                    .value_name("bool")
                    .takes_value(true)
                    .possible_values(&["0", "1"])
                    .hide_possible_values(true)
                    .help(
                        "Controls whether refinements are minimized according to subsumption rules",
                    ),
            ).arg(
                Arg::with_name("abstraction-literal-optimization")
                    .long("--abstraction-literal-optimization")
                    .default_value(default(default_options.abstraction_literal_optimization))
                    .value_name("bool")
                    .takes_value(true)
                    .possible_values(&["0", "1"])
                    .hide_possible_values(true)
                    .help(
                        "Controls whether abstractions should be optimized using subsumption rules",
                    ),
            ).arg(
                Arg::with_name("collapse-empty-scopes")
                    .long("--collapse-empty-scopes")
                    .default_value(default(default_options.collapse_empty_scopes))
                    .value_name("bool")
                    .takes_value(true)
                    .possible_values(&["0", "1"])
                    .hide_possible_values(true)
                    .help(
                        "Controls whether empty universal scopes are collapsed during mini-scoping",
                    ),
            )
    }

    fn parse_arguments(matches: &clap::ArgMatches) -> Self {
        let mut options = CaqeSolverOptions::new();
        let qdimacs_output = matches.is_present("qdimacs-output");
        let preprocessor = match matches.value_of("preprocessor") {
            None => None,
            Some(ref s) => {
                Some(QBFPreprocessor::from_str(s).unwrap())
            }
        };

        options.strong_unsat_refinement =
            matches.value_of("strong-unsat-refinement").unwrap() == "1";

        options.expansion_refinement = matches.value_of("expansion-refinement").unwrap() == "1";

        options.refinement_literal_subsumption =
            matches.value_of("refinement-literal-subsumption").unwrap() == "1";

        options.abstraction_literal_optimization = matches
            .value_of("abstraction-literal-optimization")
            .unwrap()
            == "1";

        options.collapse_empty_scopes = matches.value_of("collapse-empty-scopes").unwrap() == "1";

        CaqeSpecificSolverConfig {
            options,
            qdimacs_output,
            preprocessor,
        }
    }
}

#[cfg(feature = "statistics")]
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
enum SolverPhases {
    Preprocessing,
    Parsing,
    Initializing,
    Solving,
}

impl CaqeConfig {
    pub fn run(&self) -> Result<SolverResult, Box<Error>> {
        #[cfg(debug_assertions)]
        CombinedLogger::init(vec![
            TermLogger::new(self.verbosity, simplelog::Config::default())
                .expect("Could not initialize TermLogger"),
            //WriteLogger::new(LevelFilter::Info, Config::default(), File::create("my_rust_binary.log").unwrap()),
        ]).expect("Could not initialize logging");

        #[cfg(feature = "statistics")]
        let statistics = TimingStats::new();

        #[cfg(feature = "statistics")]
        let mut timer = statistics.start(SolverPhases::Preprocessing);

        let (matrix, partial_qdo) = preprocess(&self)?;

        #[cfg(feature = "statistics")]
        timer.stop();

        //println!("{}", matrix.dimacs());

        if matrix.conflict() {
            if self.specific.qdimacs_output {
                if let Some(partial_qdo) = partial_qdo {
                    if partial_qdo.result == SolverResult::Unsatisfiable {
                        println!("{}", partial_qdo.dimacs());
                    } else {
                        println!(
                            "{}",
                            parse::qdimacs::PartialQDIMACSCertificate::new(
                                SolverResult::Unsatisfiable,
                                partial_qdo.num_variables,
                                partial_qdo.num_clauses
                            ).dimacs()
                        );
                    }
                }
            }
            return Ok(SolverResult::Unsatisfiable);
        }

        let matrix =
            Matrix::unprenex_by_miniscoping(matrix, self.specific.options.collapse_empty_scopes);

        #[cfg(feature = "statistics")]
        let mut timer = statistics.start(SolverPhases::Initializing);

        let mut solver = CaqeSolver::new_with_options(&matrix, self.specific.options);

        #[cfg(feature = "statistics")]
        timer.stop();

        #[cfg(feature = "statistics")]
        let mut timer = statistics.start(SolverPhases::Solving);

        let result = solver.solve();

        #[cfg(feature = "statistics")]
        timer.stop();

        #[cfg(feature = "statistics")]
        {
            if self.statistics {
                println!(
                    "Preprocessing took {:?}",
                    statistics.sum(SolverPhases::Preprocessing)
                );
                println!(
                    "Initializing took {:?}",
                    statistics.sum(SolverPhases::Initializing)
                );
                println!("Solving took {:?}", statistics.sum(SolverPhases::Solving));
                solver.print_statistics();
            }
        }

        if self.specific.qdimacs_output {
            let mut solver_qdo = solver.qdimacs_output();
            if let Some(partial_qdo) = partial_qdo {
                solver_qdo.num_clauses = partial_qdo.num_clauses;
                solver_qdo.num_variables = solver_qdo.num_variables;
                if partial_qdo.result == solver_qdo.result {
                    solver_qdo.extend_assignments(partial_qdo);
                }
            }
            println!("{}", solver_qdo.dimacs());
        }

        Ok(result)
    }
}

#[derive(Debug)]
pub struct DCaqeSpecificSolverConfig {}

impl SolverSpecificConfig for DCaqeSpecificSolverConfig {
    const NAME: &'static str = "DCAQE";
    const DESC: &'static str =
        "DCAQE is a solver for dependency quantified Boolean formulas (DQBF) in DQDIMACS format.";

    fn add_arguments<'a, 'b>(app: App<'a, 'b>) -> App<'a, 'b> {
        app
    }

    fn parse_arguments(matches: &clap::ArgMatches) -> Self {
        DCaqeSpecificSolverConfig {}
    }
}

impl DCaqeConfig {
    pub fn run(&self) -> Result<SolverResult, Box<Error>> {
        #[cfg(debug_assertions)]
        CombinedLogger::init(vec![
            TermLogger::new(self.verbosity, simplelog::Config::default())
                .expect("Could not initialize TermLogger"),
            //WriteLogger::new(LevelFilter::Info, Config::default(), File::create("my_rust_binary.log").unwrap()),
        ]).expect("Could not initialize logging");

        #[cfg(feature = "statistics")]
        let statistics = TimingStats::new();

        #[cfg(feature = "statistics")]
        let mut timer = statistics.start(SolverPhases::Parsing);

        let mut file = File::open(self.filename.as_ref().unwrap())?;
        let mut contents = String::new();
        file.read_to_string(&mut contents)?;

        let mut matrix = parse::dqdimacs::parse(&contents)?;

        #[cfg(feature = "statistics")]
        timer.stop();

        //println!("{}", matrix.dimacs());

        if matrix.conflict() {
            return Ok(SolverResult::Unsatisfiable);
        }

        #[cfg(feature = "statistics")]
        let mut timer = statistics.start(SolverPhases::Initializing);

        let mut solver = DCaqeSolver::new(&mut matrix);

        #[cfg(feature = "statistics")]
        timer.stop();

        #[cfg(feature = "statistics")]
        let mut timer = statistics.start(SolverPhases::Solving);

        let result = solver.solve();

        #[cfg(feature = "statistics")]
        timer.stop();

        #[cfg(feature = "statistics")]
        {
            if self.statistics {
                println!("Parsing took {:?}", statistics.sum(SolverPhases::Parsing));
                println!(
                    "Initializing took {:?}",
                    statistics.sum(SolverPhases::Initializing)
                );
                println!("Solving took {:?}", statistics.sum(SolverPhases::Solving));
                //solver.print_statistics();
            }
        }

        Ok(result)
    }
}
