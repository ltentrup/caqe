extern crate caqe;

use std::env;
use std::process;

fn main() {
    let args: Vec<String> = env::args().collect();

    let config = caqe::Config::new(&args).unwrap_or_else(|err| {
        eprintln!("Problem parsing arguments: {}", err);
        process::exit(1);
    });

    println!("c {:?}", config);

    let result = caqe::run(config).unwrap_or_else(|err| {
        eprintln!(
            "Problem while solving: {}\ndetails: {}",
            err.description(),
            err
        );
        process::exit(1);
    });

    println!("c {:?}", result);
    process::exit(result as i32);
}
