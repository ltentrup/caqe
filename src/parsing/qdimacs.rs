use super::super::*;
use super::dimacs::*;
use std::str::FromStr;

/// Parses the QDIMACS string into its matrix representation
pub fn parse(content: &str) -> Result<Matrix<HierarchicalPrefix>, ParseError> {
    let mut lexer = DimacsTokenStream::new(content);
    let (num_variables, num_clauses) = parse_header(&mut lexer)?;
    let mut matrix = Matrix::new(num_variables, num_clauses);
    let token = parse_prefix(&mut lexer, &mut matrix)?;
    parse_matrix(&mut lexer, &mut matrix, token, num_clauses)?;
    Ok(matrix)
}

/// Parses the quantifier prefix of a QDIMACS file, e.g., `e 1 2\na 3 4\n`.
/// Returns the first token *after* the matrix.
pub fn parse_prefix(
    lexer: &mut DimacsTokenStream,
    matrix: &mut Matrix<HierarchicalPrefix>,
) -> Result<DimacsToken, ParseError> {
    loop {
        // first character after newline, either `e`, `a`, or literal (in which case we return)
        match lexer.next()? {
            DimacsToken::Quant(q) => {
                let quantifier = match q {
                    QuantKind::Exists => Ok(Quantifier::Existential),
                    QuantKind::Forall => Ok(Quantifier::Universal),
                    QuantKind::Henkin => Err(ParseError {
                        msg: format!("Henkin quantifier (`d`) are not allowed in QDIMACS"),
                        pos: lexer.pos(),
                    }),
                }?;
                let scope_id = matrix.prefix.new_scope(quantifier);

                // add variables
                loop {
                    match lexer.next()? {
                        DimacsToken::Lit(l) => {
                            if l.signed() {
                                return Err(ParseError {
                                    msg: format!(
                                        "Encountered signed literal `{:?}` in quantifier prefix",
                                        l
                                    ),
                                    pos: lexer.pos(),
                                });
                            }
                            matrix.prefix.add_variable(l.variable(), scope_id);
                        }
                        DimacsToken::Zero => {
                            // end of quantifier block
                            lexer.expect_next(DimacsToken::EOL)?;
                            break;
                        }
                        token => {
                            return Err(ParseError {
                                msg: format!("Expect literal, but found `{:?}`", token),
                                pos: lexer.pos(),
                            });
                        }
                    }
                }
            }
            DimacsToken::Lit(l) => return Ok(DimacsToken::Lit(l)),
            DimacsToken::Zero => return Ok(DimacsToken::Zero),
            DimacsToken::EOL => continue,
            DimacsToken::EOF => {
                // matrix contains no clauses
                return Ok(DimacsToken::EOF);
            }
            token => {
                return Err(ParseError {
                    msg: format!("Expect `e`, `a`, or literal, but found `{:?}`", token),
                    pos: lexer.pos(),
                })
            }
        }
    }
}

/// A partial QDIMACS certificate is an assignment to the outermost quantifiers in the QBF
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
                panic!("todo");
                //return Err(ParseError::ExpectHeaderOrComment(String::from(line)).into());
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
            None => panic!("todo"), // return Err(ParseError::NoHeaderFound.into()),
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
    fn test_simple() {
        let result = parse("p cnf 4 2\na 1 2 0\ne 3 4 0\n-1  3 0\n2 -3 -4 0\n");
        assert!(result.is_ok());
        let matrix = result.unwrap();

        // prefix
        let variables = matrix.prefix.variables();
        assert!(variables.get(1).is_universal());
        assert!(variables.get(2).is_universal());
        assert!(variables.get(3).is_existential());
        assert!(variables.get(4).is_existential());

        // clauses
        let mut clause_iter = matrix.clauses.iter();
        assert_eq!(
            clause_iter.next(),
            Some(&Clause::new(vec![(-1).into(), 3.into()]))
        );
        assert_eq!(
            clause_iter.next(),
            Some(&Clause::new(vec![(2).into(), (-3).into(), (-4).into()]))
        );
        assert_eq!(clause_iter.next(), None);
    }

    #[test]
    fn test_expect_header_or_comment() {
        let result = parse("c comment line\nsome wrong line\np cnf 0 0\n");
        assert!(result.is_err());
    }

    #[test]
    fn test_expect_header() {
        let result = parse("c comment line\n");
        assert!(result.is_err());
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
            assert!(result.is_err(), instance);
        }
    }

    #[test]
    fn test_prefix_after_clause() {
        let result = parse("p cnf 1 1\n1 2 0\ne 1 2 0\n");
        assert!(result.is_err());
    }

    #[test]
    fn test_negation_in_prefix() {
        let result = parse("p cnf 1 1\na 1 -2 0\n");
        assert!(result.is_err());
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
            assert!(result.is_err(), instance);
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
            assert!(result.is_err(), instance);
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
            assert!(result.is_ok(), instance);
        }
    }

    #[test]
    fn test_whitespaces_in_clauses() {
        let instances = vec!["p cnf 2 1\n1  2 0\n", "p cnf 2 1\n1 2 0 \n"];
        for instance in instances {
            let result = parse(instance);
            assert!(result.is_ok(), instance);
        }
    }

    #[test]
    fn test_correct_qdimacs() {
        let instances = vec!["p cnf 0 0\n", "p cnf 0 1\n0\n"];
        for instance in instances {
            let result = parse(instance);
            assert!(result.is_ok(), instance);
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
