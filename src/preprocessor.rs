use super::*;

use std::fs::File;
use std::io::SeekFrom;
use std::io::prelude::*;
use std::process::{Command, Stdio};
use std::str::FromStr;

#[derive(Debug)]
pub enum QBFPreprocessor {
    Bloqqer,
    HQSPre,
}

impl FromStr for QBFPreprocessor {
    type Err = Box<Error>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "bloqqer" => Ok(QBFPreprocessor::Bloqqer),
            "hqspre" => Ok(QBFPreprocessor::HQSPre),
            _ => panic!("unknown value {} for QBFPreprocessor", s),
        }
    }
}

impl QBFPreprocessor {
    pub fn values() -> &'static [&'static str] {
        &["bloqqer", "hqspre"]
    }
}

pub fn preprocess(
    config: &super::Config,
) -> Result<
    (
        Matrix<HierarchicalPrefix>,
        Option<qdimacs::PartialQDIMACSCertificate>,
    ),
    Box<Error>,
> {
    let mut f;
    let mut partial_qdo = None;
    match config.preprocessor {
        None => f = File::open(config.filename.clone())?,
        Some(QBFPreprocessor::Bloqqer) => {
            f = tempfile()?;
            let f_copy = f.try_clone()?;
            if config.qdimacs_output {
                let mut cert = tempfile()?;
                let cert_copy = cert.try_clone()?;
                Command::new("./bloqqer-qdo")
                    .arg("--partial-assignment=1")
                    .arg(&config.filename)
                    .stdout(f_copy)
                    .stderr(cert_copy)
                    .spawn()
                    .expect("bloqqer failed to start")
                    .wait()
                    .expect("failed to wait on bloqqer");
                cert.seek(SeekFrom::Start(0))?;
                let mut qdo = String::new();
                cert.read_to_string(&mut qdo)?;
                partial_qdo = Some(qdo.parse()?);
            } else {
                Command::new("./bloqqer")
                    .arg("--keep=0")
                    .arg(&config.filename)
                    .stdout(f_copy)
                    .stderr(Stdio::null())
                    .spawn()
                    .expect("bloqqer failed to start")
                    .wait()
                    .expect("failed to wait on bloqqer");
            };

            f.seek(SeekFrom::Start(0))?;
        }
        Some(QBFPreprocessor::HQSPre) => {
            f = tempfile()?;
            let f_copy = f.try_clone()?;
            let mut child = Command::new("./hqspre")
                .arg("--pipe")
                .arg(&config.filename)
                .stdout(f_copy)
                .stderr(Stdio::null())
                .spawn()
                .expect("hqspre failed to start");
            child.wait().expect("failed to wait on hqspre");
            f.seek(SeekFrom::Start(0))?;
        }
    }

    let mut contents = String::new();
    f.read_to_string(&mut contents)?;

    Ok((qdimacs::parse(&contents)?, partial_qdo))
}
