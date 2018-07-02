use super::super::matrix::depenendcy::*;
use super::super::*;
use super::dimacs::*;
use super::ParseError;
use std::collections::HashSet;

/// Parses the QDIMACS string into its matrix representation
pub fn parse(content: &str) -> Result<Matrix<DependencyPrefix>, ParseError> {
    let mut lexer = DimacsTokenStream::new(content);
    let (num_variables, num_clauses) = parse_header(&mut lexer)?;
    let mut matrix = Matrix::new(num_variables, num_clauses);
    let token = parse_prefix(&mut lexer, &mut matrix)?;
    parse_matrix(&mut lexer, &mut matrix, token, num_clauses)?;
    Ok(matrix)
}

/// Parses the quantifier prefix of a DQDIMACS file, e.g., `a 1 2\ne 3 0\nd 4 1\n`.
/// Returns the first token *after* the matrix.
pub fn parse_prefix(
    lexer: &mut DimacsTokenStream,
    matrix: &mut Matrix<DependencyPrefix>,
) -> Result<DimacsToken, ParseError> {
    let mut bound_universals: HashSet<Variable> = HashSet::new();

    loop {
        // first character after newline, either `e`, `a`, `d`, or literal (in which case we return)
        match lexer.next()? {
            DimacsToken::Quant(q) => match q {
                QuantKind::Exists => {
                    // dependencies are all prior bound universal variables
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
                                matrix
                                    .prefix
                                    .add_existential(l.variable(), &bound_universals);
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
                QuantKind::Forall => {
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
                                matrix.prefix.add_universal(l.variable());
                                bound_universals.insert(l.variable());
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
                QuantKind::Henkin => {
                    // the first literal is the existential variable, followed by the dependency set
                    let existential = match lexer.next()? {
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
                            l.variable()
                        }
                        token => {
                            return Err(ParseError {
                                msg: format!("Expect literal, but found `{:?}`", token),
                                pos: lexer.pos(),
                            });
                        }
                    };
                    let mut dependencies = HashSet::new();
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
                                dependencies.insert(l.variable());
                            }
                            DimacsToken::Zero => {
                                // end of quantifier block
                                lexer.expect_next(DimacsToken::EOL)?;
                                matrix.prefix.add_existential(existential, &dependencies);
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
            },
            DimacsToken::Lit(l) => return Ok(DimacsToken::Lit(l)),
            DimacsToken::Zero => return Ok(DimacsToken::Zero),
            DimacsToken::EOL => continue,
            DimacsToken::EOF => {
                // matrix contains no clauses
                return Ok(DimacsToken::EOF);
            }
            token => {
                return Err(ParseError {
                    msg: format!("Expect `e`, `a`, `d`, or literal, but found `{:?}`", token),
                    pos: lexer.pos(),
                })
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_simple() {
        let result = parse("p cnf 4 2\na 1 2 0\nd 3 1 0\ne 4 0\n-1  3 0\n2 -3 -4 0\n");
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
}
