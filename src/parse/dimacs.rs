use super::super::*;
use super::{CharIterator, ParseError, SourcePos};

#[derive(Debug, Eq, PartialEq)]
pub enum DimacsToken {
    /// p cnf header
    Header,

    /// A Literal, i.e., a signed or unsigned integer
    Lit(Literal),

    /// A zero integer, used as an ending sign
    Zero,

    /// Quantification, i.e., `e`, `a`, and `d`
    Quant(QuantKind),

    /// s cnf header
    SolutionHeader,

    /// First character of certificate line
    V,

    /// End-of-line
    EOL,

    /// End-of-file
    EOF,
}

impl Into<Literal> for DimacsToken {
    fn into(self) -> Literal {
        match self {
            DimacsToken::Zero => Literal::new(0_u32, false),
            DimacsToken::Lit(l) => l,
            _ => panic!("cannot convert {:?} into Literal", self),
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
pub enum QuantKind {
    Exists,
    Forall,
    Henkin,
}

pub struct DimacsTokenStream<'a> {
    chars: CharIterator<'a>,
}

impl<'a> DimacsTokenStream<'a> {
    pub fn new(content: &'a str) -> DimacsTokenStream<'a> {
        DimacsTokenStream {
            chars: CharIterator::new(content),
        }
    }

    pub fn next_token(&mut self) -> Result<DimacsToken, ParseError> {
        while let Some(c) = self.chars.next() {
            match c {
                'c' => {
                    // comment line, ignore until next newline
                    self.chars.skip_while(|c| *c != '\n');
                }
                'p' => {
                    // DIMACS header
                    self.chars.expect_str(" cnf ")?;
                    return Ok(DimacsToken::Header);
                }
                's' => {
                    // DIMACS solution header
                    self.chars.expect_str(" cnf ")?;
                    return Ok(DimacsToken::SolutionHeader);
                }
                'e' => return Ok(DimacsToken::Quant(QuantKind::Exists)),
                'a' => return Ok(DimacsToken::Quant(QuantKind::Forall)),
                'd' => return Ok(DimacsToken::Quant(QuantKind::Henkin)),
                '0' => return Ok(DimacsToken::Zero),
                '-' => {
                    // negated literal
                    return Ok(DimacsToken::Lit(self.chars.read_literal('-')?));
                }
                c if c.is_ascii_digit() => {
                    // digit
                    return Ok(DimacsToken::Lit(self.chars.read_literal(c)?));
                }
                'V' => return Ok(DimacsToken::V),
                '\n' => return Ok(DimacsToken::EOL),
                ' ' => continue,
                _ => {
                    return Err(ParseError {
                        msg: format!("Encountered unknown token `{}` during lexing", c),
                        pos: self.chars.pos,
                    });
                }
            }
        }
        // end of file
        Ok(DimacsToken::EOF)
    }

    pub fn expect_next(&mut self, token: &DimacsToken) -> Result<(), ParseError> {
        self.next_token().and_then(|next| {
            if next == *token {
                Ok(())
            } else {
                Err(ParseError {
                    msg: format!("Expected token `{:?}` but found `{:?}`", token, next),
                    pos: self.chars.pos,
                })
            }
        })
    }

    pub fn pos(&self) -> SourcePos {
        self.chars.pos
    }
}

/// Parses the `p cnf NUM NUM` header and returns number of variables and number of clauses
pub fn parse_header(lexer: &mut DimacsTokenStream) -> Result<(usize, usize), ParseError> {
    // first non-EOL token has to be `p cnf ` header
    loop {
        match lexer.next_token()? {
            DimacsToken::EOL => continue,
            DimacsToken::Header => break,
            token => {
                return Err(ParseError {
                    msg: format!("Expect `p cnf`, but found `{:?}`", token),
                    pos: lexer.pos(),
                });
            }
        }
    }
    //lexer.expect_next(&DimacsToken::EOL);
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
    Ok((num_variables.into(), num_clauses.into()))
}

pub fn parse_matrix<P: Prefix>(
    lexer: &mut DimacsTokenStream,
    matrix: &mut Matrix<P>,
    mut current: DimacsToken,
    num_clauses_expected: usize,
) -> Result<(), ParseError> {
    let mut literals: Vec<Literal> = Vec::new();
    let mut num_clauses_read = 0;

    loop {
        match current {
            DimacsToken::Zero => {
                // end of clause
                lexer.expect_next(&DimacsToken::EOL)?;
                matrix.add(Clause::new(literals));
                literals = Vec::new();
                num_clauses_read += 1;
            }
            DimacsToken::Lit(l) => {
                literals.push(l);
            }
            DimacsToken::EOL => {
                // End-of-line without prior `0` marker
                // either wrong format, or `EOF` follows
                if !literals.is_empty() {
                    // End-of-line during clause read
                    return Err(ParseError {
                        msg: "Unexpected end of line while reading clause".to_string(),
                        pos: lexer.pos(),
                    });
                }
            }
            DimacsToken::EOF => {
                if !literals.is_empty() {
                    // End-of-file during clause read
                    return Err(ParseError {
                        msg: "Unexpected end of input while reading clause".to_string(),
                        pos: lexer.pos(),
                    });
                }
                if num_clauses_expected != num_clauses_read {
                    return Err(ParseError {
                        msg: format!(
                            "Expected {} clauses, but found {}",
                            num_clauses_expected, num_clauses_read
                        ),
                        pos: lexer.pos(),
                    });
                }
                return Ok(());
            }
            _ => {
                return Err(ParseError {
                    msg: format!("Unexpected token `{:?}` while reading clause", current),
                    pos: lexer.pos(),
                });
            }
        }
        current = lexer.next_token()?;
    }
}

#[cfg(test)]
mod tests {

    use super::matrix::hierarchical::HierarchicalPrefix;
    use super::*;

    #[test]
    fn test_lexer_simple() {
        let mut stream = DimacsTokenStream::new("p cnf 0 0\n");
        assert_eq!(stream.next_token(), Ok(DimacsToken::Header));
        assert_eq!(stream.next_token(), Ok(DimacsToken::Zero));
        assert_eq!(stream.next_token(), Ok(DimacsToken::Zero));
        assert_eq!(stream.next_token(), Ok(DimacsToken::EOL));
        assert_eq!(stream.next_token(), Ok(DimacsToken::EOF));
    }

    #[test]
    fn test_lexer_all() {
        let mut stream = DimacsTokenStream::new("c comment\np cnf 0 0\ne a d\n-1 1 0\n");
        assert_eq!(stream.next_token(), Ok(DimacsToken::Header));
        assert_eq!(stream.next_token(), Ok(DimacsToken::Zero));
        assert_eq!(stream.next_token(), Ok(DimacsToken::Zero));
        assert_eq!(stream.next_token(), Ok(DimacsToken::EOL));

        assert_eq!(
            stream.next_token(),
            Ok(DimacsToken::Quant(QuantKind::Exists))
        );
        assert_eq!(
            stream.next_token(),
            Ok(DimacsToken::Quant(QuantKind::Forall))
        );
        assert_eq!(
            stream.next_token(),
            Ok(DimacsToken::Quant(QuantKind::Henkin))
        );
        assert_eq!(stream.next_token(), Ok(DimacsToken::EOL));

        assert_eq!(stream.next_token(), Ok(DimacsToken::Lit((-1).into())));
        assert_eq!(stream.next_token(), Ok(DimacsToken::Lit(1.into())));
        assert_eq!(stream.next_token(), Ok(DimacsToken::Zero));
        assert_eq!(stream.next_token(), Ok(DimacsToken::EOL));
        assert_eq!(stream.next_token(), Ok(DimacsToken::EOF));
    }

    #[test]
    fn test_lexer_error() {
        let mut stream = DimacsTokenStream::new("x");
        assert!(stream.next_token().is_err());

        let mut stream = DimacsTokenStream::new("-a");
        assert!(stream.next_token().is_err());

        let mut stream = DimacsTokenStream::new("- ");
        assert!(stream.next_token().is_err());

        let mut stream = DimacsTokenStream::new("--1");
        assert!(stream.next_token().is_err());
    }

    #[test]
    fn test_parse_matrix() {
        let mut lexer = DimacsTokenStream::new("-1  2 0\n2 -3 -4 0\n");
        let mut matrix = Matrix::<HierarchicalPrefix>::new(4, 2);
        let current = lexer.next_token().unwrap();
        assert!(parse_matrix(&mut lexer, &mut matrix, current, 2).is_ok());
        let mut clause_iter = matrix.clauses.iter();
        assert_eq!(
            clause_iter.next(),
            Some(&Clause::new(vec![(-1).into(), 2.into()]))
        );
        assert_eq!(
            clause_iter.next(),
            Some(&Clause::new(vec![(2).into(), (-3).into(), (-4).into()]))
        );
        assert_eq!(clause_iter.next(), None);
    }

    #[test]
    fn test_parse_header() {
        let mut lexer = DimacsTokenStream::new("p cnf 2 4\n");
        assert_eq!(parse_header(&mut lexer), Ok((2, 4)));
    }
}
