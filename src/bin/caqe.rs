use std::{env, process};

fn main() {
    let args: Vec<String> = env::args().collect();

    let config = caqe::CaqeConfig::new(&args);

    println!("c {:?}", config);

    let result = config.run().unwrap_or_else(|err| {
        eprintln!("Problem while solving: {}", err);
        process::exit(1);
    });

    println!("c {:?}", result);
    process::exit(result as i32);
}
