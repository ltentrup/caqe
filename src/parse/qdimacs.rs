use super::super::matrix::hierarchical::*;
use super::super::*;
use super::dimacs::*;
use super::ParseError;
use std::str::FromStr;

/// Parses the QDIMACS string into its matrix representation
pub fn parse(content: &str) -> Result<Matrix<HierarchicalPrefix>, ParseError> {
    let mut lexer = DimacsTokenStream::new(content);
    let (num_variables, num_clauses) = parse_header(&mut lexer)?;
    let mut matrix = Matrix::new(num_variables, num_clauses);
    let token = parse_prefix(&mut lexer, &mut matrix)?;
    parse_matrix(&mut lexer, &mut matrix, token, num_clauses)?;
    matrix.prefix.compute_dependencies();

    // in the case the last scope is universal, we remove it
    let last_scope = matrix.prefix.last_scope();
    if matrix.prefix.scopes[last_scope.to_usize()].quant == Quantifier::Universal {
        matrix.prefix.remove_scope(last_scope);
    }
    Ok(matrix)
}

/// Parses the quantifier prefix of a QDIMACS file, e.g., `e 1 2\na 3 4\n`.
/// Returns the first token *after* the matrix.
pub(crate) fn parse_prefix(
    lexer: &mut DimacsTokenStream,
    matrix: &mut Matrix<HierarchicalPrefix>,
) -> Result<DimacsToken, ParseError> {
    let mut pref_scope_id = *matrix.prefix.roots.first().expect("root cannot be empty");
    loop {
        // first character after newline, either `e`, `a`, or literal (in which case we return)
        match lexer.next_token()? {
            DimacsToken::Quant(q) => {
                let quantifier = match q {
                    QuantKind::Exists => Ok(Quantifier::Existential),
                    QuantKind::Forall => Ok(Quantifier::Universal),
                    QuantKind::Henkin => Err(ParseError {
                        msg: "Henkin quantifier (`d`) are not allowed in QDIMACS".to_string(),
                        pos: lexer.pos(),
                    }),
                }?;
                let scope_id = matrix.prefix.new_scope(pref_scope_id, quantifier);

                // add variables
                loop {
                    match lexer.next_token()? {
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
                            lexer.expect_next(&DimacsToken::EOL)?;
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

                pref_scope_id = scope_id;
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
                });
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
    #[must_use]
    pub fn new(result: SolverResult, num_variables: usize, num_clauses: usize) -> Self {
        Self {
            result,
            num_variables,
            num_clauses,
            assignments: Vec::new(),
        }
    }

    pub fn add_assignment(&mut self, assignment: Literal) {
        if self.assignments.binary_search(&assignment).is_ok() {
            return;
        }
        self.assignments.push(assignment);
        self.assignments.sort();
    }

    pub fn extend_assignments(&mut self, qdo: Self) {
        for assignment in qdo.assignments {
            self.add_assignment(assignment);
        }
    }
}

/// Parses the `s cnf RESULT NUM NUM` header and returns result, number of variables, and number of clauses
pub fn parse_qdimacs_certificate_header(
    lexer: &mut DimacsTokenStream,
) -> Result<(SolverResult, usize, usize), ParseError> {
    // first non-EOL token has to be `s cnf ` header
    loop {
        match lexer.next_token()? {
            DimacsToken::EOL => continue,
            DimacsToken::SolutionHeader => break,
            token => {
                return Err(ParseError {
                    msg: format!("Expect `s cnf`, but found `{:?}`", token),
                    pos: lexer.pos(),
                });
            }
        }
    }
    let result = match lexer.next_token()? {
        DimacsToken::Zero => SolverResult::Unsatisfiable,
        DimacsToken::Lit(l) => {
            if l.signed() {
                return Err(ParseError {
                    msg: "Malformed `s cnf` header, found negative value for number of variables"
                        .to_string(),
                    pos: lexer.pos(),
                });
            }
            if l.variable() == 1_u32.into() {
                if l.signed() {
                    SolverResult::Unknown
                } else {
                    SolverResult::Satisfiable
                }
            } else {
                return Err(ParseError {
                    msg: format!(
                        "Malformed `s cnf` header, expect `-1`, `0`, or `1` for result, found {}",
                        l.dimacs()
                    ),
                    pos: lexer.pos(),
                });
            }
        }
        token => {
            return Err(ParseError {
                msg: format!(
                    "Malformed `s cnf` header, expected number of variables, found `{:?}`",
                    token
                ),
                pos: lexer.pos(),
            });
        }
    };
    let num_variables = match lexer.next_token()? {
        DimacsToken::Zero => 0_u32.into(),
        DimacsToken::Lit(l) => {
            if l.signed() {
                return Err(ParseError {
                    msg: "Malformed `p cnf` header, found negative value for number of variables"
                        .to_string(),
                    pos: lexer.pos(),
                });
            }
            l.variable()
        }
        token => {
            return Err(ParseError {
                msg: format!(
                    "Malformed `p cnf` header, expected number of variables, found `{:?}`",
                    token
                ),
                pos: lexer.pos(),
            });
        }
    };
    let num_clauses = match lexer.next_token()? {
        DimacsToken::Zero => 0_u32.into(),
        DimacsToken::Lit(l) => {
            if l.signed() {
                return Err(ParseError {
                    msg: "Malformed `p cnf` header, found negative value for number of clauses"
                        .to_string(),
                    pos: lexer.pos(),
                });
            }
            l.variable()
        }
        token => {
            return Err(ParseError {
                msg: format!(
                    "Malformed `p cnf` header, expected number of clauses, found `{:?}`",
                    token
                ),
                pos: lexer.pos(),
            });
        }
    };
    Ok((result, num_variables.into(), num_clauses.into()))
}

impl FromStr for PartialQDIMACSCertificate {
    type Err = Box<ParseError>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut lexer = DimacsTokenStream::new(s);

        let (result, num_variables, num_clauses) = parse_qdimacs_certificate_header(&mut lexer)?;
        let mut certificate = Self::new(result, num_variables, num_clauses);

        loop {
            match lexer.next_token()? {
                DimacsToken::EOL => {
                    // ignore empty lines
                    continue;
                }
                DimacsToken::EOF => {
                    break;
                }
                DimacsToken::V => {
                    // V <literal> 0\n
                    match lexer.next_token()? {
                        DimacsToken::Lit(l) => {
                            certificate.add_assignment(l);
                        }
                        token => {
                            return Err(ParseError {
                                msg: format!(
                                    "Encountered {:?} instead of literal in certificate line",
                                    token
                                ),
                                pos: lexer.pos(),
                            }
                            .into());
                        }
                    }
                    lexer.expect_next(&DimacsToken::Zero)?;
                    lexer.expect_next(&DimacsToken::EOL)?;
                }
                token => {
                    return Err(ParseError {
                        msg: format!("Certificate line should start with `V`, found {:?}", token),
                        pos: lexer.pos(),
                    }
                    .into());
                }
            }
        }

        Ok(certificate)
    }
}

impl Dimacs for PartialQDIMACSCertificate {
    #[must_use]
    fn dimacs(&self) -> String {
        let mut dimacs = String::new();
        dimacs.push_str(&format!(
            "s cnf {} {} {}\n",
            self.result.dimacs(),
            self.num_variables,
            self.num_clauses,
        ));
        for literal in &self.assignments {
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

        let v1 = Variable::from(1_u32);
        let v2 = Variable::from(2_u32);
        let v3 = Variable::from(3_u32);
        let v4 = Variable::from(4_u32);

        // prefix
        let variables = matrix.prefix.variables();
        assert!(variables.get(v1).is_universal());
        assert!(variables.get(v2).is_universal());
        assert!(variables.get(v3).is_existential());
        assert!(variables.get(v4).is_existential());

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
            assignments: vec![Literal::new(2_u32, true), Literal::new(3_u32, false)],
        };
        let dimacs_output = certificate.dimacs();
        assert_eq!(dimacs_output.as_str(), "s cnf 1 4 3\nV -2 0\nV 3 0\n");
        let parsed: PartialQDIMACSCertificate = dimacs_output.parse().unwrap();
        assert_eq!(certificate, parsed);
    }
}
