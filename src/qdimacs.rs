use super::*;
use std::error::Error;
use std::fmt;

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
        if line.starts_with("c") {
            // comment line
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
        // a line looks as follows:
        // quantifier: e 1 2 0 or a 1 2 0
        // clause: 1 2 0
        let mut clause_ended = false;
        let mut chunks = line.split(|char| char == ' ');
        let mut literals: Vec<Literal> = Vec::new();
        let mut scope_id: Option<ScopeId> = None;

        for (i, chunk) in chunks.enumerate() {
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
                    let clause = Clause::new(literals);
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
                literals.push(Literal::from(literal));
            }
        }
        if !clause_ended {
            return Err(ParseError::WrongClause(String::from(line)).into());
        }
    }

    if num_clauses_read != num_clauses {
        return Err(ParseError::WrongNumberOfClauses(num_clauses, num_clauses_read).into());
    }

    println!("{:?}", matrix);

    Ok(matrix)
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
    fn test_correct_qdimacs() {
        let instances = vec!["p cnf 0 0\n", "p cnf 0 1\n0\n"];
        for instance in instances {
            let result = parse(instance);
            debug_assert!(result.is_ok(), instance);
        }
    }

}
