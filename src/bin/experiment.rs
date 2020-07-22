use std::{env, process};

fn main() {
    let args: Vec<String> = env::args().collect();

    let config = caqe::experiment::ExperimentConfig::new(&args).unwrap_or_else(|err| {
        eprintln!("Error during execution: {}", err);
        process::exit(1);
    });

    config.run().unwrap_or_else(|err| {
        eprintln!("Error during execution: {}", err);
        process::exit(1);
    });
}
