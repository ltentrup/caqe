// extern crates
#[macro_use]
extern crate log;
extern crate simplelog;
#[macro_use]
extern crate text_io;
extern crate tempfile;

use simplelog::*;

use tempfile::tempfile;

// Rust stdlib
use std::error::Error;

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
    pub preprocessor: Option<QBFPreprocessor>,
}

impl Config {
    pub fn new(args: &[String]) -> Result<Config, &'static str> {
        if args.len() < 2 {
            return Err("expect file name");
        }

        let mut verbosity = LevelFilter::Warn;
        let mut filename = None;
        let mut options = CaqeSolverOptions::new();
        let mut qdimacs_output = false;
        let mut preprocessor = None;
        for arg in args {
            match arg.as_ref() {
                "-v" => verbosity = LevelFilter::Trace,
                "--sur" => options.strong_unsat_refinement = !options.strong_unsat_refinement,
                "--er" => options.expansion_refinement = !options.expansion_refinement,
                "--rls" => {
                    options.refinement_literal_subsumption = !options.refinement_literal_subsumption
                }
                "--alo" => {
                    options.abstraction_literal_optimization =
                        !options.abstraction_literal_optimization
                }
                "--qdo" => qdimacs_output = true,
                "--bloqqer" => preprocessor = Some(QBFPreprocessor::Bloqqer),
                _ => {
                    if arg.starts_with("-") {
                        return Err("unknown argument");
                    } else {
                        filename = Some(arg.clone());
                    }
                }
            }
        }

        let filename = match filename {
            None => return Err("no filename given"),
            Some(f) => f,
        };

        Ok(Config {
            filename,
            verbosity,
            options,
            qdimacs_output,
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
    let mut timer = statistics.unwrap().start(SolverPhases::Preprocessing);

    let (matrix, partial_qdo) = preprocess(&config)?;

    #[cfg(feature = "statistics")]
    timer.stop();

    //println!("{}", matrix.dimacs());

    if matrix.conflict() {
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
        println!("Parsing took {:?}", statistics.sum(SolverPhases::Parsing));
        println!(
            "Initializing took {:?}",
            statistics.sum(SolverPhases::Initializing)
        );
        println!("Solving took {:?}", statistics.sum(SolverPhases::Solving));
        solver.print_statistics();
    }

    if config.qdimacs_output {
        println!("{}", solver.qdimacs_output().dimacs());
    }

    Ok(result)
}
