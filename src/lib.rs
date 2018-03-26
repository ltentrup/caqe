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

mod dimacs;
use dimacs::*;

mod qdimacs;

// Command line parsing

#[derive(Debug)]
pub struct Config {
    pub filename: String,
}

impl Config {
    pub fn new(args: &[String]) -> Result<Config, &'static str> {
        if args.len() != 2 {
            return Err("expect only file name as agument");
        }

        let filename = args[1].clone();

        Ok(Config { filename })
    }
}

pub fn run(config: Config) -> Result<(), Box<Error>> {
    let mut f = File::open(config.filename)?;
    let mut contents = String::new();
    f.read_to_string(&mut contents)?;

    let matrix = qdimacs::parse(&contents)?;

    println!("{}", matrix.dimacs());

    Ok(())
}
