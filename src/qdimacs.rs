use super::*;
use std::error::Error;
use std::fmt;
use std::str::FromStr;

#[derive(Debug, PartialEq, Eq)]
pub enum ParseError {
    ExpectHeaderOrComment(String),
    NoHeaderFound,
    WrongHeader(String),
    UnexpectedQuantification(String),
    WrongClause(String),
    UnexpectedNegation(String),
    WrongNumberOfClauses(usize, usize),
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &ParseError::ExpectHeaderOrComment(ref line) => {
                write!(f, "line that caused error: {}", line)
            }
            &ParseError::NoHeaderFound => Ok(()),
            &ParseError::WrongHeader(ref line) => write!(f, "line that caused error: {}", line),
            &ParseError::UnexpectedQuantification(ref line) => {
                write!(f, "line that caused error: {}", line)
            }
            &ParseError::WrongClause(ref line) => write!(f, "line that caused error: {}", line),
            &ParseError::UnexpectedNegation(ref line) => {
                write!(f, "line that caused error: {}", line)
            }
            &ParseError::WrongNumberOfClauses(was, read) => write!(
                f,
                "read {} clauses, but {} were specified in prefix",
                read, was
            ),
        }
    }
}

impl Error for ParseError {
    fn description(&self) -> &str {
        match self {
            &ParseError::ExpectHeaderOrComment(ref _line) => "expect header or comment",
            &ParseError::NoHeaderFound => "missing required `p cnf` header",
            &ParseError::WrongHeader(ref _line) => "wrong header format, expect `p cnf NUM NUM`",
            &ParseError::UnexpectedQuantification(ref _line) => {
                "quantification has to be in prefix"
            }
            &ParseError::WrongClause(ref _line) => "clause is malformed",
            &ParseError::UnexpectedNegation(ref _line) => {
                "negation is not allowed in quantifier prefix"
            }
            &ParseError::WrongNumberOfClauses(_was, _read) => {
                "instance contains a different number of clauses than specified"
            }
        }
    }

    fn cause(&self) -> Option<&Error> {
        Some(self)
    }
}

pub fn parse(content: &str) -> Result<Matrix<HierarchicalPrefix>, Box<Error>> {
    let mut lines = content.lines();

    let mut initial_matrix: Option<Matrix<HierarchicalPrefix>> = None;
    let mut num_clauses: Option<usize> = None;

    // parse header
    while let Some(line) = lines.next() {
        if line.starts_with("c") || line.is_empty() {
            // comment or empty line
            continue;
        } else if line.starts_with("p") {
            // header line
            let mut num_var: Option<usize> = None;
            let mut chunks = line.split(|c| c == ' ');
            for (i, chunk) in chunks.enumerate() {
                match i {
                    0 => {
                        if chunk != "p" {
                            return Err(ParseError::WrongHeader(String::from(line)).into());
                        }
                    }
                    1 => {
                        if chunk != "cnf" {
                            return Err(ParseError::WrongHeader(String::from(line)).into());
                        }
                    }
                    2 => match chunk.parse::<usize>() {
                        Ok(num) => num_var = Some(num),
                        Err(_) => {
                            return Err(ParseError::WrongHeader(String::from(line)).into());
                        }
                    },
                    3 => match chunk.parse::<usize>() {
                        Ok(num) => num_clauses = Some(num),
                        Err(_) => {
                            return Err(ParseError::WrongHeader(String::from(line)).into());
                        }
                    },
                    _ => return Err(ParseError::WrongHeader(String::from(line)).into()),
                }
            }
            match (num_var, num_clauses) {
                (Some(variables), Some(clauses)) => {
                    initial_matrix = Some(Matrix::new(variables, clauses))
                }
                (_, _) => return Err(ParseError::WrongHeader(String::from(line)).into()),
            }
            break;
        } else {
            return Err(ParseError::ExpectHeaderOrComment(String::from(line)).into());
        }
    }

    let mut matrix = match initial_matrix {
        Some(m) => m,
        None => return Err(ParseError::NoHeaderFound.into()),
    };

    let num_clauses = num_clauses.unwrap();

    // parse quantifier prefix and clauses
    let mut in_prefix = true;
    let mut num_clauses_read = 0;
    while let Some(line) = lines.next() {
        if line.is_empty() {
            continue;
        }

        // a line looks as follows:
        // quantifier: e 1 2 0 or a 1 2 0
        // clause: 1 2 0
        let mut clause_ended = false;
        let mut chunks = line.split(|char| char == ' ');
        let mut literals: Vec<Literal> = Vec::new();
        let mut scope_id: Option<ScopeId> = None;

        for (i, chunk) in chunks.enumerate() {
            if chunk.is_empty() {
                continue;
            }
            if clause_ended {
                return Err(ParseError::WrongClause(String::from(line)).into());
            }
            if i == 0 {
                if chunk == "a" || chunk == "e" {
                    // quantifier prefix
                    if !in_prefix {
                        return Err(ParseError::UnexpectedQuantification(String::from(line)).into());
                    }
                    let quantifier: Quantifier;
                    if chunk == "a" {
                        quantifier = Quantifier::Universal;
                    } else {
                        debug_assert!(chunk == "e");
                        quantifier = Quantifier::Existential;
                    }
                    scope_id = Some(matrix.prefix.new_scope(quantifier));
                    continue;
                } else {
                    in_prefix = false;
                }
            }
            let literal: i32;
            match chunk.parse::<i32>() {
                Ok(l) => literal = l,
                Err(_) => {
                    return Err(ParseError::WrongClause(String::from(line)).into());
                }
            };
            if literal == 0 {
                if scope_id.is_none() {
                    let mut clause = Clause::new(literals);
                    clause.reduce_universal_qbf(&matrix.prefix);
                    matrix.add(clause);
                    num_clauses_read += 1;
                }

                clause_ended = true;
                scope_id = None;
                literals = Vec::new();
                continue;
            }

            if let Some(scope_id) = scope_id {
                if literal < 0 {
                    return Err(ParseError::UnexpectedNegation(String::from(line)).into());
                }
                matrix.prefix.add_variable(literal as Variable, scope_id);
            } else {
                // clause
                let l = Literal::from(literal);
                literals.push(l);
                // check of variable is bounded
                if !matrix.prefix.variables().get(l.variable()).is_bound() {
                    matrix.prefix.add_variable(l.variable(), 0);
                }
            }
        }
        if !clause_ended {
            return Err(ParseError::WrongClause(String::from(line)).into());
        }
    }

    if num_clauses_read != num_clauses {
        return Err(ParseError::WrongNumberOfClauses(num_clauses, num_clauses_read).into());
    }

    //println!("{:?}", matrix);

    Ok(matrix)
}

/// A partial QDIMACS certifciate is an assignment to the outermost quantifiers in the QBF
#[derive(Debug, PartialEq, Eq)]
pub struct PartialQDIMACSCertificate {
    pub result: SolverResult,
    pub num_variables: usize,
    pub num_clauses: usize,
    assignments: Vec<Literal>,
}

impl PartialQDIMACSCertificate {
    pub fn new(
        result: SolverResult,
        num_variables: usize,
        num_clauses: usize,
    ) -> PartialQDIMACSCertificate {
        PartialQDIMACSCertificate {
            result,
            num_variables,
            num_clauses,
            assignments: Vec::new(),
        }
    }

    pub fn add_assignment(&mut self, assignment: Literal) {
        assert!(self.assignments.binary_search(&assignment).is_err());
        self.assignments.push(assignment);
        self.assignments.sort();
    }

    pub fn extend_assignments(&mut self, qdo: PartialQDIMACSCertificate) {
        for assignment in qdo.assignments {
            self.add_assignment(assignment);
        }
    }
}

impl FromStr for PartialQDIMACSCertificate {
    type Err = Box<ParseError>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut lines = s.lines();
        let mut certificate = None;
        while let Some(line) = lines.next() {
            if line.starts_with("c") || line.is_empty() {
                // comment or empty line
                continue;
            } else if !line.starts_with("s cnf") {
                return Err(ParseError::ExpectHeaderOrComment(String::from(line)).into());
            }
            // read header line
            let result: i32;
            let num_variables: usize;
            let num_clauses: usize;
            scan!(line.bytes() => "s cnf {} {} {}", result, num_variables, num_clauses);
            let result = if result == 0 {
                SolverResult::Unsatisfiable
            } else if result == 1 {
                SolverResult::Satisfiable
            } else {
                SolverResult::Unknown
            };
            certificate = Some(PartialQDIMACSCertificate::new(
                result,
                num_variables,
                num_clauses,
            ));
            break;
        }
        let mut certificate = match certificate {
            None => return Err(ParseError::NoHeaderFound.into()),
            Some(c) => c,
        };
        while let Some(line) = lines.next() {
            if line.is_empty() {
                // skip empty lines
                continue;
            }
            // line has the form `V [-]var 0\n`
            let literal: i32 = read!("V {} 0", line.bytes());
            certificate.add_assignment(Literal::from(literal));
        }
        Ok(certificate)
    }
}

impl Dimacs for PartialQDIMACSCertificate {
    fn dimacs(&self) -> String {
        let mut dimacs = String::new();
        dimacs.push_str(&format!(
            "s cnf {} {} {}\n",
            self.result.dimacs(),
            self.num_variables,
            self.num_clauses,
        ));
        for literal in self.assignments.iter() {
            dimacs.push_str(&format!("V {} 0\n", literal.dimacs()));
        }
        dimacs
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_expect_header_or_comment() {
        let result = parse("c comment line\nsome wrong line\np cnf 0 0\n");
        debug_assert!(result.is_err());
        let error = result.err().unwrap();
        assert_eq!(
            error.description(),
            ParseError::ExpectHeaderOrComment(String::new()).description()
        );
    }

    #[test]
    fn test_expect_header() {
        let result = parse("c comment line\n");
        debug_assert!(result.is_err());
        let error = result.err().unwrap();
        assert_eq!(error.description(), ParseError::NoHeaderFound.description());
    }

    #[test]
    fn test_wrong_header() {
        let instances = vec![
            "pcnf 0 0\n",
            "p\n",
            "pcnf\n",
            "p cnf\n",
            "p cnf 1\n",
            "p cnf -1 0\n",
        ];
        for instance in instances {
            let result = parse(instance);
            debug_assert!(result.is_err());
            let error = result.err().unwrap();
            assert_eq!(
                error.description(),
                ParseError::WrongHeader(String::new()).description()
            );
        }
    }

    #[test]
    fn test_prefix_after_clause() {
        let result = parse("p cnf 1 1\n1 2 0\ne 1 2 0\n");
        debug_assert!(result.is_err());
        let error = result.err().unwrap();
        assert_eq!(
            error.description(),
            ParseError::UnexpectedQuantification(String::new()).description()
        );
    }

    #[test]
    fn test_negation_in_prefix() {
        let result = parse("p cnf 1 1\na 1 -2 0\n");
        debug_assert!(result.is_err());
        let error = result.err().unwrap();
        assert_eq!(
            error.description(),
            ParseError::UnexpectedNegation(String::new()).description()
        );
    }

    #[test]
    fn test_wrong_clauses() {
        let instances = vec![
            "p cnf 2 1\n1 0 2\n",
            "p cnf 2 1\n1 2\n",
            "p cnf 2 1\n1 2 a 0\n",
        ];
        for instance in instances {
            let result = parse(instance);
            debug_assert!(result.is_err());
            let error = result.err().unwrap();
            assert_eq!(
                error.description(),
                ParseError::WrongClause(String::new()).description()
            );
        }
    }

    #[test]
    fn test_wrong_number_of_clauses() {
        let instances = vec![
            "p cnf 2 2\n1 2 0\n",          // less
            "p cnf 2 1\n1 2 0\n-1 -2 0\n", // more
        ];
        for instance in instances {
            let result = parse(instance);
            debug_assert!(result.is_err());
            let error = result.err().unwrap();
            assert_eq!(
                error.description(),
                ParseError::WrongNumberOfClauses(0, 0).description()
            );
        }
    }

    #[test]
    fn test_empty_lines() {
        let instances = vec![
            "\np cnf 1 1\n1 2 0\n", // empty line in front
            "p cnf 1 1\n\n1 2 0\n", // empty line before clause
            "p cnf 1 1\n1 2 0\n\n", // empty line after clause
        ];
        for instance in instances {
            let result = parse(instance);
            debug_assert!(result.is_ok(), instance);
        }
    }

    #[test]
    fn test_whitespaces_in_clauses() {
        let instances = vec!["p cnf 2 1\n1  2 0\n", "p cnf 2 1\n1 2 0 \n"];
        for instance in instances {
            let result = parse(instance);
            debug_assert!(result.is_ok(), instance);
        }
    }

    #[test]
    fn test_correct_qdimacs() {
        let instances = vec!["p cnf 0 0\n", "p cnf 0 1\n0\n"];
        for instance in instances {
            let result = parse(instance);
            debug_assert!(result.is_ok(), instance);
        }
    }

    #[test]
    fn test_qdimacs_output() {
        let certificate = PartialQDIMACSCertificate {
            result: SolverResult::Satisfiable,
            num_variables: 4,
            num_clauses: 3,
            assignments: vec![Literal::new(2, true), Literal::new(3, false)],
        };
        let dimacs_output = certificate.dimacs();
        assert_eq!(dimacs_output.as_str(), "s cnf 1 4 3\nV -2 0\nV 3 0\n");
        let parsed: PartialQDIMACSCertificate = dimacs_output.parse().unwrap();
        assert_eq!(certificate, parsed);
    }

}
