// extern crates
#[macro_use]
extern crate log;
extern crate simplelog;
#[macro_use]
extern crate text_io;
extern crate clap;
extern crate tempfile;

use simplelog::*;

use tempfile::tempfile;
use clap::{App, Arg, SubCommand};

// Rust stdlib
use std::error::Error;
use std::str::FromStr;

// modules
mod literal;
use literal::*;
pub use self::literal::Literal; // re-export literals

mod clause;
use clause::*;

mod matrix;
use matrix::*;

mod caqe;
use caqe::*;

mod dimacs;
use dimacs::*;

mod solver;
use solver::*;

mod preprocessor;
use preprocessor::*;

mod qdimacs;

mod utils;

use utils::statistics::TimingStats;

// Command line parsing

#[derive(Debug)]
pub struct Config {
    pub filename: String,
    pub verbosity: LevelFilter,
    pub options: CaqeSolverOptions,
    pub qdimacs_output: bool,
    pub statistics: bool,
    pub preprocessor: Option<QBFPreprocessor>,
}

impl Config {
    pub fn new(args: &[String]) -> Result<Config, &'static str> {
        let mut options = CaqeSolverOptions::new();

        let default = |val| match val {
            true => "1",
            false => "0",
        };

        let mut flags = App::new("CAQE")
            .version(env!("CARGO_PKG_VERSION"))
            .author(env!("CARGO_PKG_AUTHORS"))
            .about("CAQE is a solver for quantified Boolean formulas given in QDIMACS file format")
            .arg(
                Arg::with_name("INPUT")
                    .help("Sets the input file to use")
                    .required(true)
                    .index(1),
            )
            .arg(
                Arg::with_name("preprocessor")
                    .help("Sets the preprocessor to use")
                    .long("--preprocessor")
                    .takes_value(true)
                    .possible_values(QBFPreprocessor::values()),
            )
            .arg(
                Arg::with_name("qdimacs-output")
                    .long("--qdo")
                    .help("Prints QDIMACS output (partial assignment) after solving"),
            )
            .arg(
                Arg::with_name("strong-unsat-refinement")
                    .long("--strong-unsat-refinement")
                    .default_value(default(options.strong_unsat_refinement))
                    .value_name("bool")
                    .takes_value(true)
                    .possible_values(&["0", "1"])
                    .hide_possible_values(true)
                    .help("Controls whether strong unsat refinement should be used"),
            )
            .arg(
                Arg::with_name("expansion-refinement")
                    .long("--expansion-refinement")
                    .default_value(default(options.expansion_refinement))
                    .value_name("bool")
                    .takes_value(true)
                    .possible_values(&["0", "1"])
                    .hide_possible_values(true)
                    .help("Controls whether expansion refinement should be used"),
            )
            .arg(
                Arg::with_name("refinement-literal-subsumption")
                    .long("--refinement-literal-subsumption")
                    .default_value(default(options.refinement_literal_subsumption))
                    .value_name("bool")
                    .takes_value(true)
                    .possible_values(&["0", "1"])
                    .hide_possible_values(true)
                    .help(
                        "Controls whether refinements are minimized according to subsumption rules",
                    ),
            )
            .arg(
                Arg::with_name("abstraction-literal-optimization")
                    .long("--abstraction-literal-optimization")
                    .default_value(default(options.abstraction_literal_optimization))
                    .value_name("bool")
                    .takes_value(true)
                    .possible_values(&["0", "1"])
                    .hide_possible_values(true)
                    .help(
                        "Controls whether abstractions should be optimized using subsumption rules",
                    ),
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
        let matches = flags.get_matches_from(args);

        // file name is mandatory
        let filename = String::from(matches.value_of("INPUT").unwrap());

        let verbosity = match matches.occurrences_of("v") {
            0 => LevelFilter::Warn,
            1 => LevelFilter::Info,
            2 => LevelFilter::Debug,
            3 | _ => LevelFilter::Trace,
        };

        let qdimacs_output = matches.is_present("qdimacs-output");

        let statistics = matches.is_present("statistics");

        let preprocessor = match matches.value_of("preprocessor") {
            None => None,
            Some(ref s) => Some(QBFPreprocessor::from_str(s).unwrap()),
        };

        options.strong_unsat_refinement =
            matches.value_of("strong-unsat-refinement").unwrap() == "1";

        options.expansion_refinement = matches.value_of("expansion-refinement").unwrap() == "1";

        options.refinement_literal_subsumption =
            matches.value_of("refinement-literal-subsumption").unwrap() == "1";

        options.abstraction_literal_optimization = matches
            .value_of("abstraction-literal-optimization")
            .unwrap() == "1";

        Ok(Config {
            filename,
            verbosity,
            options,
            qdimacs_output,
            statistics,
            preprocessor,
        })
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
enum SolverPhases {
    Preprocessing,
    Initializing,
    Solving,
}

pub fn run(config: Config) -> Result<SolverResult, Box<Error>> {
    #[cfg(debug_assertions)]
    CombinedLogger::init(vec![
        TermLogger::new(config.verbosity, simplelog::Config::default()).unwrap(),
        //WriteLogger::new(LevelFilter::Info, Config::default(), File::create("my_rust_binary.log").unwrap()),
    ]).unwrap();

    #[cfg(feature = "statistics")]
    let statistics = TimingStats::new();

    #[cfg(feature = "statistics")]
    let mut timer = statistics.start(SolverPhases::Preprocessing);

    let (matrix, partial_qdo) = preprocess(&config)?;

    #[cfg(feature = "statistics")]
    timer.stop();

    //println!("{}", matrix.dimacs());

    if matrix.conflict() {
        if config.qdimacs_output {
            if let Some(partial_qdo) = partial_qdo {
                if partial_qdo.result == SolverResult::Unsatisfiable {
                    println!("{}", partial_qdo.dimacs());
                } else {
                    println!(
                        "{}",
                        qdimacs::PartialQDIMACSCertificate::new(
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

    let matrix = Matrix::unprenex_by_miniscoping(matrix);

    #[cfg(feature = "statistics")]
    let mut timer = statistics.start(SolverPhases::Initializing);

    let mut solver = CaqeSolver::new_with_options(&matrix, config.options);

    #[cfg(feature = "statistics")]
    timer.stop();

    #[cfg(feature = "statistics")]
    let mut timer = statistics.start(SolverPhases::Solving);

    let result = solver.solve();

    #[cfg(feature = "statistics")]
    timer.stop();

    #[cfg(feature = "statistics")]
    {
        if config.statistics {
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

    if config.qdimacs_output {
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
