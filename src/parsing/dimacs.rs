use super::super::matrix::hierarchical::*;
use std::error::Error;
use std::fmt;
use std::str::Chars;

use super::super::*;

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
            DimacsToken::Zero => Literal::new(0, false),
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

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct SourcePos {
    line: usize,
    column: usize,
}

impl SourcePos {
    fn new() -> SourcePos {
        SourcePos { line: 0, column: 0 }
    }

    fn advance(&mut self, len: usize) {
        self.column += len;
    }

    fn newline(&mut self) {
        self.line += 1;
        self.column = 0;
    }
}

impl fmt::Display for SourcePos {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

pub struct DimacsTokenStream<'a> {
    chars: CharIterator<'a>,
}

#[derive(Debug, Eq, PartialEq)]
pub struct ParseError {
    pub msg: String,
    pub pos: SourcePos,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "parse error: {} at {}", self.description(), self.pos)
    }
}

impl Error for ParseError {
    fn description(&self) -> &str {
        self.msg.as_str()
    }

    fn cause(&self) -> Option<&Error> {
        Some(self)
    }
}

impl<'a> DimacsTokenStream<'a> {
    pub fn new(content: &'a str) -> DimacsTokenStream<'a> {
        DimacsTokenStream {
            chars: CharIterator::new(content),
        }
    }

    pub fn next(&mut self) -> Result<DimacsToken, ParseError> {
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
                    return self.chars.read_literal('-');
                }
                c if c.is_ascii_digit() => {
                    // digit
                    return self.chars.read_literal(c);
                }
                'V' => return Ok(DimacsToken::V),
                '\n' => return Ok(DimacsToken::EOL),
                ' ' => continue,
                _ => {
                    return Err(ParseError {
                        msg: format!("Encountered unknown token `{}` during lexing", c),
                        pos: self.chars.pos,
                    })
                }
            }
        }
        // end of file
        return Ok(DimacsToken::EOF);
    }

    pub fn expect_next(&mut self, token: DimacsToken) -> Result<(), ParseError> {
        self.next().and_then(|next| {
            if next != token {
                Err(ParseError {
                    msg: format!("Expected token `{:?}` but found `{:?}`", token, next),
                    pos: self.chars.pos,
                })
            } else {
                Ok(())
            }
        })
    }

    pub fn pos(&self) -> SourcePos {
        self.chars.pos
    }
}

struct CharIterator<'a> {
    chars: Chars<'a>,
    pos: SourcePos,
}

impl<'a> CharIterator<'a> {
    fn new(content: &'a str) -> CharIterator<'a> {
        CharIterator {
            chars: content.chars(),
            pos: SourcePos::new(),
        }
    }

    fn next(&mut self) -> Option<char> {
        match self.chars.next() {
            None => None,
            Some(c) => {
                if c == '\n' {
                    self.pos.newline()
                } else {
                    self.pos.advance(1)
                }
                Some(c)
            }
        }
    }

    fn read_literal(&mut self, first: char) -> Result<DimacsToken, ParseError> {
        let signed;
        let mut value;
        if first == '-' {
            signed = true;
            value = None;
        } else if let Some(digit) = first.to_digit(10) {
            signed = false;
            value = Some(digit);
        } else {
            panic!(
                "Expect first character of literal to be a digit or `-`, were given `{}`",
                first
            );
        }
        while let Some(c) = self.next() {
            if c.is_ascii_whitespace() {
                break;
            }
            if let Some(digit) = c.to_digit(10) {
                value = match value {
                    None => Some(digit),
                    Some(prev) => Some(prev * 10 + digit),
                }
            } else {
                return Err(ParseError {
                    msg: format!(
                        "Encountered non-digit character `{}` while parsing literal",
                        c
                    ),
                    pos: self.pos,
                });
            }
        }
        if let Some(value) = value {
            return Ok(DimacsToken::Lit(Literal::new(value, signed)));
        } else {
            assert!(first == '-');
            return Err(ParseError {
                msg: format!("Expect digits following `-` character"),
                pos: self.pos,
            });
        }
    }

    fn expect_char(&mut self, expected: char) -> Result<(), ParseError> {
        match self.next() {
            None => Err(ParseError {
                msg: format!("Unexpected end of input"),
                pos: self.pos,
            }),
            Some(c) => {
                if c != expected {
                    Err(ParseError {
                        msg: format!("Expected character `{}`, but found `{}`", expected, c),
                        pos: self.pos,
                    })
                } else {
                    Ok(())
                }
            }
        }
    }

    fn expect_str(&mut self, expected: &str) -> Result<(), ParseError> {
        for c in expected.chars() {
            self.expect_char(c)?;
        }
        Ok(())
    }

    fn skip_while<P>(&mut self, predicate: P)
    where
        P: Fn(&char) -> bool,
    {
        while let Some(c) = self.next() {
            if !predicate(&c) {
                break;
            }
        }
    }
}

/// Parses the `p cnf NUM NUM` header and returns number of variables and number of clauses
pub fn parse_header(lexer: &mut DimacsTokenStream) -> Result<(usize, usize), ParseError> {
    // first non-EOL token has to be `p cnf ` header
    loop {
        match lexer.next()? {
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
    //lexer.expect_next(DimacsToken::EOL);
    let num_variables = match lexer.next()? {
        DimacsToken::Zero => 0,
        DimacsToken::Lit(l) => {
            if l.signed() {
                return Err(ParseError {
                    msg: format!(
                        "Malformed `p cnf` header, found negative value for number of variables"
                    ),
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
            })
        }
    };
    let num_clauses = match lexer.next()? {
        DimacsToken::Zero => 0,
        DimacsToken::Lit(l) => {
            if l.signed() {
                return Err(ParseError {
                    msg: format!(
                        "Malformed `p cnf` header, found negative value for number of clauses"
                    ),
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
            })
        }
    };
    Ok((num_variables as usize, num_clauses as usize))
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
                lexer.expect_next(DimacsToken::EOL)?;
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
                        msg: format!("Unexpected end of line while reading clause"),
                        pos: lexer.pos(),
                    });
                }
            }
            DimacsToken::EOF => {
                if !literals.is_empty() {
                    // End-of-file during clause read
                    return Err(ParseError {
                        msg: format!("Unexpected end of input while reading clause"),
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
                })
            }
        }
        current = lexer.next()?;
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_lexer_simple() {
        let mut stream = DimacsTokenStream::new("p cnf 0 0\n");
        assert_eq!(stream.next(), Ok(DimacsToken::Header));
        assert_eq!(stream.next(), Ok(DimacsToken::Zero));
        assert_eq!(stream.next(), Ok(DimacsToken::Zero));
        assert_eq!(stream.next(), Ok(DimacsToken::EOL));
        assert_eq!(stream.next(), Ok(DimacsToken::EOF));
    }

    #[test]
    fn test_lexer_all() {
        let mut stream = DimacsTokenStream::new("c comment\np cnf 0 0\ne a d\n-1 1 0\n");
        assert_eq!(stream.next(), Ok(DimacsToken::Header));
        assert_eq!(stream.next(), Ok(DimacsToken::Zero));
        assert_eq!(stream.next(), Ok(DimacsToken::Zero));
        assert_eq!(stream.next(), Ok(DimacsToken::EOL));

        assert_eq!(stream.next(), Ok(DimacsToken::Quant(QuantKind::Exists)));
        assert_eq!(stream.next(), Ok(DimacsToken::Quant(QuantKind::Forall)));
        assert_eq!(stream.next(), Ok(DimacsToken::Quant(QuantKind::Henkin)));
        assert_eq!(stream.next(), Ok(DimacsToken::EOL));

        assert_eq!(stream.next(), Ok(DimacsToken::Lit((-1).into())));
        assert_eq!(stream.next(), Ok(DimacsToken::Lit(1.into())));
        assert_eq!(stream.next(), Ok(DimacsToken::Zero));
        assert_eq!(stream.next(), Ok(DimacsToken::EOL));
        assert_eq!(stream.next(), Ok(DimacsToken::EOF));
    }

    #[test]
    fn test_lexer_error() {
        let mut stream = DimacsTokenStream::new("x");
        assert!(stream.next().is_err());

        let mut stream = DimacsTokenStream::new("-a");
        assert!(stream.next().is_err());

        let mut stream = DimacsTokenStream::new("- ");
        assert!(stream.next().is_err());

        let mut stream = DimacsTokenStream::new("--1");
        assert!(stream.next().is_err());
    }

    #[test]
    fn test_parse_matrix() {
        let mut lexer = DimacsTokenStream::new("-1  2 0\n2 -3 -4 0\n");
        let mut matrix = Matrix::<HierarchicalPrefix>::new(4, 2);
        let current = lexer.next().unwrap();
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
