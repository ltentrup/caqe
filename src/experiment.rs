use crate::{
    parse::qdimacs,
    solve::{
        caqe::{CaqeSolver, SolverOptions},
        Solver, SolverResult,
    },
};
use atomicwrites::{AllowOverwrite, AtomicFile};
use clap::{App, Arg, SubCommand};
use indicatif::{ProgressBar, ProgressStyle};
use serde::{Deserialize, Serialize};
use std::{
    cmp::Ordering,
    collections::HashMap,
    error::Error,
    fs::File,
    io::Read as _,
    sync::{
        atomic::{AtomicBool, Ordering as AtomicOrdering},
        mpsc::{channel, RecvTimeoutError},
        Arc,
    },
    thread,
    time::{Duration, Instant},
};

#[allow(clippy::module_name_repetitions)]
#[derive(Debug, Clone)]
pub struct ExperimentConfig {
    config_file: String,
    mode: ExperimentMode,
}

#[allow(clippy::module_name_repetitions)]
#[derive(Debug, Clone, Copy)]
pub enum ExperimentMode {
    Run,
    Analyze,
    Compare(usize, usize),
}

#[allow(clippy::module_name_repetitions)]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExperimentResult {
    result: SolverResult,
    iterations: usize,
    duration: Duration,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct Results {
    benchmarks: Vec<String>,
    configs: Vec<SolverOptions>,
    /// indexed by `configs`
    results: Vec<HashMap<String, ExperimentResult>>,
}

impl ExperimentConfig {
    #[allow(unreachable_code)]
    #[allow(unused_variables)]
    pub fn new(args: &[String]) -> Result<Self, Box<dyn Error>> {
        let flags = App::new("experiment")
            .version(env!("CARGO_PKG_VERSION"))
            .author(env!("CARGO_PKG_AUTHORS"))
            .about("This utility helps finding the best solver configuration for a given benchmark set.")
            .arg(Arg::with_name("config")
                .long("--config")
                .short("-c")
                .help("Sets the path of the config file")
                .required(true)
                .takes_value(true)
            ).subcommand(
                SubCommand::with_name("create")
                    .about("Creates a new experiment")
                    .arg(
                        Arg::with_name("benchmarks")
                        .long("--benchmarks")
                        .help("Sets the benchmarks to use")
                        .required(true)
                        .takes_value(true)
                        .multiple(true)
                    )
            ).subcommand(SubCommand::with_name("continue").about("Continues an experiment"))
            .subcommand(SubCommand::with_name("analyze").about("Analyzes an experiment"))
            .subcommand(SubCommand::with_name("compare").about("Compares two solver configurations")
                .arg(
                        Arg::with_name("solver-configs")
                        .help("Index of the solver configs that should be compared")
                        .required(true)
                        .takes_value(true)
                        .multiple(true)
                    )
            );

        #[cfg(not(feature = "statistics"))]
        panic!("Feature `statistics` needs to be enabled");

        let matches = flags.get_matches_from(args);
        let config_file: &str = matches.value_of("config").unwrap();

        Ok(match matches.subcommand() {
            ("create", Some(matches)) => {
                let benchmarks: Vec<String> = matches
                    .values_of("benchmarks")
                    .unwrap()
                    .map(std::string::ToString::to_string)
                    .collect();
                eprintln!("Selected {:?} benchmarks", benchmarks.len());

                eprintln!("Write config to `{:?}`", config_file);

                let config = Results::new(benchmarks, SolverOptions::default());
                let file = File::create(config_file)?;
                serde_json::to_writer_pretty(file, &config)?;

                Self {
                    mode: ExperimentMode::Run,
                    config_file: config_file.to_string(),
                }
            }
            ("continue", Some(_)) => Self {
                mode: ExperimentMode::Run,
                config_file: config_file.to_string(),
            },
            ("analyze", Some(_)) => Self {
                mode: ExperimentMode::Analyze,
                config_file: config_file.to_string(),
            },
            ("compare", Some(matches)) => {
                let cfgs: Vec<usize> = matches
                    .values_of("solver-configs")
                    .unwrap()
                    .map(|s| {
                        s.parse::<usize>().unwrap_or_else(|_| {
                            panic!("Expected index of solver config, found {}", s);
                        })
                    })
                    .collect();
                assert_eq!(cfgs.len(), 2);

                Self {
                    mode: ExperimentMode::Compare(cfgs[0], cfgs[1]),
                    config_file: config_file.to_string(),
                }
            }
            (cmd, _) => unreachable!("unknown subcommand `{}`", cmd),
        })
    }

    pub fn run(&self) -> Result<(), Box<dyn Error>> {
        match self.mode {
            ExperimentMode::Run => {
                self.run_experiment()?;
                self.analyze_experiment()
            }
            ExperimentMode::Analyze => self.analyze_experiment(),
            ExperimentMode::Compare(a, b) => self.compare_solver_configs(a, b),
        }
    }

    fn run_experiment(&self) -> Result<(), Box<dyn Error>> {
        let mut file = File::open(&self.config_file)?;
        let mut contents = String::new();
        file.read_to_string(&mut contents)?;

        let mut results: Results = serde_json::from_str(&contents)?;

        assert_eq!(results.configs.len(), results.results.len());

        let timeout = Duration::from_secs(60);

        let num_open = results.benchmarks.iter().fold(0, |val, bench| {
            val + results
                .configs
                .iter()
                .enumerate()
                .fold(0, |val, (config_idx, _)| {
                    val + if let Some(result) = results.results[config_idx].get(&bench.clone()) {
                        // re-run experiment only if timeout has increased
                        match result.result {
                            SolverResult::Satisfiable | SolverResult::Unsatisfiable => 0,
                            SolverResult::Unknown if result.duration >= timeout => 0,
                            SolverResult::Unknown => {
                                assert!(result.duration < timeout);
                                1
                            }
                        }
                    } else {
                        1
                    }
                })
        });
        let progress_bar = ProgressBar::new(num_open);
        progress_bar.set_style(
            ProgressStyle::default_bar().template("{wide_bar} {pos}/{len} {eta} remaining"),
        );
        progress_bar.enable_steady_tick(100);

        for benchmark in &results.benchmarks {
            for (config_idx, &config) in results.configs.iter().enumerate() {
                if let Some(result) = results.results[config_idx].get(&benchmark.clone()) {
                    // re-run experiment only if timeout has increased
                    match result.result {
                        SolverResult::Satisfiable | SolverResult::Unsatisfiable => continue,
                        SolverResult::Unknown if result.duration >= timeout => continue,
                        SolverResult::Unknown => {
                            assert!(result.duration < timeout);
                        }
                    }
                }
                //println!("run {:?}", benchmark);

                let mut benchmark_file = File::open(benchmark)?;
                let mut file_contents = String::new();
                benchmark_file.read_to_string(&mut file_contents)?;

                let mut matrix = qdimacs::parse(&file_contents)?;

                let (tx, rx) = channel();

                let interrupt_handler = Arc::new(AtomicBool::new(false));

                let interrupted = interrupt_handler.clone();

                let child = thread::spawn(move || {
                    let start = Instant::now();
                    if config.miniscoping {
                        matrix.unprenex_by_miniscoping();
                    }
                    if config.expansion.dependency_schemes {
                        matrix.refl_res_path_dep_scheme();
                    }
                    let mut solver = CaqeSolver::new_with_options(matrix, config);
                    solver.set_interrupt(interrupted);
                    let result = solver.solve();
                    #[allow(unused_assignments)]
                    #[allow(unused_mut)]
                    let mut iterations = 0;

                    #[cfg(feature = "statistics")]
                    {
                        iterations = solver.get_iterations();
                    }

                    tx.send(ExperimentResult::new(result, iterations, start.elapsed()))
                        .expect("Unable to send on channel");
                });

                match rx.recv_timeout(timeout) {
                    Ok(result) => {
                        results.results[config_idx].insert(benchmark.clone(), result);
                    }
                    Err(RecvTimeoutError::Timeout) => {
                        interrupt_handler.store(true, AtomicOrdering::Relaxed);

                        results.results[config_idx].insert(
                            benchmark.clone(),
                            ExperimentResult::new(SolverResult::Unknown, 0, timeout),
                        );
                    }
                    _ => panic!("channel error"),
                }

                progress_bar.inc(1);

                let af = AtomicFile::new(&self.config_file, AllowOverwrite);
                af.write(|f| serde_json::to_writer_pretty(f, &results))?;

                //serde_json::to_writer_pretty(File::create(&self.config_file)?, &results)?;

                // some work here
                let _res = child.join();
            }
        }

        progress_bar.finish();

        Ok(())
    }

    fn analyze_experiment(&self) -> Result<(), Box<dyn Error>> {
        let mut file = File::open(&self.config_file)?;
        let mut contents = String::new();
        file.read_to_string(&mut contents)?;

        let results: Results = serde_json::from_str(&contents)?;

        // check for inconsistent results
        for benchmark in &results.benchmarks {
            let mut sat = Vec::new();
            let mut unsat = Vec::new();
            for (config_idx, result) in results.results.iter().enumerate() {
                if let Some(res) = result.get(benchmark) {
                    match res.result {
                        SolverResult::Satisfiable => sat.push(config_idx),
                        SolverResult::Unsatisfiable => unsat.push(config_idx),
                        _ => {}
                    }
                }
            }
            if !sat.is_empty() && !unsat.is_empty() {
                println!(
                    "inconsistent result {}: sat {:?}, unsat {:?}",
                    benchmark, sat, unsat
                );
            }
        }

        for (config_idx, _) in results.configs.iter().enumerate() {
            let mut solved = 0;
            let mut sat = 0;
            let mut unsat = 0;
            let mut iterations = 0;

            for result in results.results[config_idx].values() {
                match result.result {
                    SolverResult::Unknown => continue,
                    SolverResult::Satisfiable => {
                        sat += 1;
                    }
                    SolverResult::Unsatisfiable => {
                        unsat += 1;
                    }
                }
                solved += 1;
                iterations += result.iterations;
            }

            println!(
                "cfg {}, solved {}, sat {}, unsat {}, iter {}",
                config_idx, solved, sat, unsat, iterations
            );
        }
        Ok(())
    }

    #[allow(clippy::too_many_lines)]
    fn compare_solver_configs(
        &self,
        base_idx: usize,
        other_idx: usize,
    ) -> Result<(), Box<dyn Error>> {
        let mut file = File::open(&self.config_file)?;
        let mut contents = String::new();
        file.read_to_string(&mut contents)?;

        let results: Results = serde_json::from_str(&contents)?;

        //println!("cfg {}: {}", base_idx, serde_json::to_string_pretty(&results.configs[base_idx])?);
        //println!("cfg {}: {}", other_idx, serde_json::to_string_pretty(&results.configs[other_idx])?);

        println!(
            "{}",
            colored_diff::PrettyDifference {
                expected: &serde_json::to_string_pretty(&results.configs[base_idx])?,
                actual: &serde_json::to_string_pretty(&results.configs[other_idx])?
            }
        );

        let mut equal_num_iterations = 0;
        let mut base_less_num_iterations = 0;
        let mut other_less_num_iterations = 0;
        let mut equal_solving_times = 0;
        let mut base_less_solving_time = 0;
        let mut other_less_solving_time = 0;
        let mut unique_base = Vec::new();
        let mut unique_other = Vec::new();
        for benchmark in &results.benchmarks {
            let base_res = if let Some(res) = results.results[base_idx].get(benchmark) {
                res
            } else {
                continue;
            };
            let other_res = if let Some(res) = results.results[other_idx].get(benchmark) {
                res
            } else {
                continue;
            };

            match (base_res.result, other_res.result) {
                (SolverResult::Unknown, SolverResult::Unknown) => {
                    if base_res.duration != other_res.duration {
                        eprintln!(
                            "inconsistent timeouts on `{}`: {:?} vs. {:?}",
                            benchmark, base_res.duration, other_res.duration
                        );
                    }
                    continue;
                }
                (SolverResult::Unknown, _) => {
                    unique_other.push((benchmark.clone(), other_res.clone()));
                    continue;
                }
                (_, SolverResult::Unknown) => {
                    unique_base.push((benchmark.clone(), base_res.clone()));
                    continue;
                }
                (SolverResult::Satisfiable, SolverResult::Satisfiable)
                | (SolverResult::Unsatisfiable, SolverResult::Unsatisfiable) => {}
                (a, b) => eprintln!(
                    "inconsistent results on `{}`: {:?} vs. {:?}",
                    benchmark, a, b
                ),
            }
            match base_res.iterations.cmp(&other_res.iterations) {
                Ordering::Equal => equal_num_iterations += 1,
                Ordering::Less => base_less_num_iterations += 1,
                Ordering::Greater => other_less_num_iterations += 1,
            }
            if let Some(diff) = base_res.duration.checked_sub(other_res.duration) {
                if diff > Duration::from_secs(1) {
                    other_less_solving_time += 1;
                } else {
                    equal_solving_times += 1;
                }
            } else if let Some(diff) = other_res.duration.checked_sub(base_res.duration) {
                if diff > Duration::from_secs(1) {
                    base_less_solving_time += 1;
                } else {
                    equal_solving_times += 1;
                }
            } else {
                unreachable!();
            }
        }

        println!(
            "\niterations: equal {}, cfg {} less {}, cfg {} less {}",
            equal_num_iterations,
            base_idx,
            base_less_num_iterations,
            other_idx,
            other_less_num_iterations
        );
        println!(
            "solving time: equal {}, cfg {} less {}, cfg {} less {}",
            equal_solving_times,
            base_idx,
            base_less_solving_time,
            other_idx,
            other_less_solving_time
        );
        println!(
            "uniquely solved: cfg  {}: {}, cfg {}: {}",
            base_idx,
            unique_base.len(),
            other_idx,
            unique_other.len()
        );

        if !unique_base.is_empty() {
            println!("\nunique cfg {}", base_idx);
            for (bench, res) in &unique_base {
                println!("* {}: {:?}", bench, res);
            }
        }
        if !unique_other.is_empty() {
            println!("\nunique cfg {}", other_idx);
            for (bench, res) in &unique_other {
                println!("* {}: {:?}", bench, res);
            }
        }

        Ok(())
    }
}

impl ExperimentResult {
    fn new(result: SolverResult, iterations: usize, duration: Duration) -> Self {
        Self {
            result,
            iterations,
            duration,
        }
    }
}

impl Results {
    fn new(benchmarks: Vec<String>, options: SolverOptions) -> Self {
        Self {
            benchmarks,
            configs: vec![options],
            results: vec![HashMap::new()],
        }
    }
}
