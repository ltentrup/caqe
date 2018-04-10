#[macro_use]
extern crate log;
extern crate simplelog;

use simplelog::*;

use std::error::Error;
use std::fs::File;
use std::io::prelude::*;

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

mod qdimacs;

mod utils;

// Command line parsing

#[derive(Debug)]
pub struct Config {
    pub filename: String,
    pub verbosity: LevelFilter,
    pub options: CaqeSolverOptions,
}

impl Config {
    pub fn new(args: &[String]) -> Result<Config, &'static str> {
        if args.len() < 2 {
            return Err("expect file name");
        }

        let mut verbosity = LevelFilter::Info;
        let mut filename = None;
        let mut options = CaqeSolverOptions::new();
        for arg in args {
            match arg.as_ref() {
                "-v" => verbosity = LevelFilter::Trace,
                "-alo" => {
                    options.abstraction_literal_optimization =
                        !options.abstraction_literal_optimization
                }
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
        })
    }
}

pub fn run(config: Config) -> Result<SolverResult, Box<Error>> {
    let mut f = File::open(config.filename)?;
    let mut contents = String::new();
    f.read_to_string(&mut contents)?;

    #[cfg(debug_assertions)]
    CombinedLogger::init(vec![
        TermLogger::new(config.verbosity, simplelog::Config::default()).unwrap(),
        //WriteLogger::new(LevelFilter::Info, Config::default(), File::create("my_rust_binary.log").unwrap()),
    ]).unwrap();

    let matrix = qdimacs::parse(&contents)?;

    //println!("{}", matrix.dimacs());

    if matrix.conflict() {
        return Ok(SolverResult::Unsatisfiable);
    }

    let mut solver = CaqeSolver::new_with_options(&matrix, config.options);

    let result = solver.solve();

    #[cfg(feature = "statistics")]
    solver.print_statistics();

    Ok(result)
}
