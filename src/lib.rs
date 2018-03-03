use std::ops;
use std::error::Error;
use std::fs::File;
use std::io::prelude::*;

mod qdimacs;

pub type Variable = u32;

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Debug)]
pub struct Literal {
    x: u32,
}

impl Literal {
    pub fn new(variable: Variable, signed: bool) -> Literal {
        Literal {
            x: variable << 1 | (signed as u32),
        }
    }

    /// Returns true if `Literal` is signed
    ///
    /// # Examples
    ///
    /// ```
    /// assert!(qbf::Literal::new(0, true).signed());
    /// assert!(!qbf::Literal::new(0, false).signed());
    /// ```
    pub fn signed(&self) -> bool {
        (self.x & 1) != 0
    }

    pub fn unsigned(&self) -> Literal {
        Literal { x: self.x & !1 }
    }

    pub fn variable(&self) -> Variable {
        self.x >> 1
    }

    pub fn dimacs(&self) -> i32 {
        let base = self.variable() as i32;
        if self.signed() {
            -base
        } else {
            base
        }
    }
}

impl ops::Neg for Literal {
    type Output = Literal;

    fn neg(self) -> Literal {
        Literal { x: self.x ^ 1 }
    }
}

#[cfg(test)]
mod literal_tests {

    use std::mem;

    use super::*;

    #[test]
    fn size_of_literal() {
        let result = mem::size_of::<Literal>();
        assert!(
            result == 4,
            "Size of `Literal` should be 4 bytes, was `{}`",
            result
        );
    }
}

#[derive(PartialEq, Eq, Debug)]
pub struct Clause {
    literals: Vec<Literal>,
}

impl Clause {
    pub fn new(literals: Vec<Literal>, normalize: bool) -> Clause {
        if normalize {
            let mut l = literals;
            l.sort();
            l.dedup();
            Clause { literals: l }
        } else {
            Clause { literals: literals }
        }
    }

    pub fn new_normalized(literals: Vec<Literal>) -> Clause {
        Clause::new(literals, true)
    }

    pub fn len(&self) -> usize {
        self.literals.len()
    }

    pub fn is_tautology(&self) -> bool {
        for (i, &el1) in self.literals.iter().enumerate() {
            if i + 1 >= self.literals.len() {
                break;
            }
            let el2 = self.literals[i + 1];
            if el1 == -el2 {
                return true;
            }
        }
        true
    }
}

#[cfg(test)]
mod clause_tests {
    use std::mem;

    use super::*;

    #[test]
    fn size_of_clause() {
        let result = mem::size_of::<Clause>();
        assert!(
            result == 24,
            "Size of `Clause` should be 24 bytes, was `{}`",
            result
        );
    }

    #[test]
    fn clause_normalization() {
        let lit1 = Literal::new(0, false);
        let lit2 = Literal::new(1, false);
        let literals = vec![lit2, lit1, lit2];
        let clause1 = Clause::new_normalized(literals);
        let clause2 = Clause::new(vec![lit1, lit2], false);
        assert_eq!(clause1, clause2);
    }
}

pub trait Prefix {
    fn new(num_variables: usize) -> Self;
}

#[derive(Debug)]
pub struct Matrix<P: Prefix> {
    prefix: P,
    clauses: Vec<Clause>,
}

impl<P: Prefix> Matrix<P> {
    fn new(num_variables: usize, num_clauses: usize) -> Matrix<P> {
        Matrix {
            prefix: P::new(num_variables),
            clauses: Vec::with_capacity(num_clauses),
        }
    }
}

pub type ScopeId = i32;

#[derive(Debug)]
pub struct VariableInfo {
    scope: ScopeId,
}

#[derive(Debug)]
pub struct Scope {
    variables: Vec<Variable>,
}

#[derive(Debug)]
pub struct HierarchicalPrefix {
    variables: Vec<VariableInfo>,
    scopes: Vec<Scope>,
}

impl Prefix for HierarchicalPrefix {
    fn new(num_variables: usize) -> Self {
        HierarchicalPrefix {
            variables: Vec::with_capacity(num_variables + 1),
            scopes: vec![
                Scope {
                    variables: Vec::new(),
                },
            ],
        }
    }
}

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

    let matrix = qdimacs::parse(&contents);

    Ok(())
}
