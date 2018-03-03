extern crate qbf;

use std::env;
use std::process;

fn main() {
    let args: Vec<String> = env::args().collect();

    let config = qbf::Config::new(&args).unwrap_or_else(|err| {
        eprintln!("Problem parsing arguments: {}", err);
        process::exit(1);
    });

    println!("{:?}", config);

    let result = qbf::run(config).unwrap_or_else(|err| {
        eprintln!("Problem while solving: {}", err);
        process::exit(1);
    });

    println!("{:?}", result);
}
