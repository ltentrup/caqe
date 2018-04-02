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

// Command line parsing

#[derive(Debug)]
pub struct Config {
    pub filename: String,
    pub verbosity: LevelFilter,
}

impl Config {
    pub fn new(args: &[String]) -> Result<Config, &'static str> {
        if args.len() < 2 {
            return Err("expect file name");
        }

        let mut verbosity = LevelFilter::Info;
        let mut filename = None;
        for arg in args {
            match arg.as_ref() {
                "-v" => verbosity = LevelFilter::Trace,
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
        })
    }
}

pub fn run(config: Config) -> Result<SolverResult, Box<Error>> {
    let mut f = File::open(config.filename)?;
    let mut contents = String::new();
    f.read_to_string(&mut contents)?;

    CombinedLogger::init(vec![
        TermLogger::new(config.verbosity, simplelog::Config::default()).unwrap(),
        //WriteLogger::new(LevelFilter::Info, Config::default(), File::create("my_rust_binary.log").unwrap()),
    ]).unwrap();

    let matrix = qdimacs::parse(&contents)?;

    //println!("{}", matrix.dimacs());

    let mut solver = CaqeSolver::new(&matrix);

    let result = solver.solve();

    Ok(result)
}
