use std::str::Chars;

use super::super::*;

#[derive(Debug, Eq, PartialEq)]
enum DimacsToken {
    /// p cnf header
    Header,

    /// A Literal, i.e., a signed or unsigned integer
    Literal(Literal),

    /// A zero integer, used as an ending sign
    Zero,

    /// Quantification, i.e., `e`, `a`, and `d`
    Quantifier(QuantifierKind),

    /// End-of-line
    EOL,

    /// End-of-file
    EOF,
}

impl Into<Literal> for DimacsToken {
    fn into(self) -> Literal {
        match self {
            DimacsToken::Literal(l) => l,
            DimacsToken::Zero => Literal::new(0, false),
            _ => panic!("cannot convert {:?} into Literal", self),
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
enum QuantifierKind {
    Exists,
    Forall,
    Henkin,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct SourcePos {
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

struct DimacsTokenStream<'a> {
    chars: CharIterator<'a>,
}

#[derive(Debug, Eq, PartialEq)]
struct ParseError {
    msg: String,
    pos: SourcePos,
}

impl<'a> DimacsTokenStream<'a> {
    fn new(content: &'a str) -> DimacsTokenStream<'a> {
        DimacsTokenStream {
            chars: CharIterator::new(content),
        }
    }

    fn next(&mut self) -> Result<DimacsToken, ParseError> {
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
                'e' => return Ok(DimacsToken::Quantifier(QuantifierKind::Exists)),
                'a' => return Ok(DimacsToken::Quantifier(QuantifierKind::Forall)),
                'd' => return Ok(DimacsToken::Quantifier(QuantifierKind::Henkin)),
                '0' => return Ok(DimacsToken::Zero),
                '-' => {
                    // negated literal
                    return self.chars.read_literal('-');
                }
                c if c.is_ascii_digit() => {
                    // digit
                    return self.chars.read_literal(c);
                }
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

    fn expect_next(&mut self, token: DimacsToken) -> Result<(), ParseError> {
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

    fn pos(&self) -> SourcePos {
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
            if c == ' ' {
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
            return Ok(DimacsToken::Literal(Literal::new(value, signed)));
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

fn parse_matrix<P: Prefix>(
    lexer: &mut DimacsTokenStream,
    matrix: &mut Matrix<P>,
    mut current: DimacsToken,
) -> Result<(), ParseError> {
    let mut literals: Vec<Literal> = Vec::new();

    loop {
        match current {
            DimacsToken::Zero => {
                // end of clause
                lexer.expect_next(DimacsToken::EOL)?;
                matrix.add(Clause::new(literals));
                literals = Vec::new();
            }
            DimacsToken::Literal(l) => {
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
                continue;
            }
            DimacsToken::EOF => {
                if !literals.is_empty() {
                    // End-of-file during clause read
                    return Err(ParseError {
                        msg: format!("Unexpected end of input while reading clause"),
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

        assert_eq!(
            stream.next(),
            Ok(DimacsToken::Quantifier(QuantifierKind::Exists))
        );
        assert_eq!(
            stream.next(),
            Ok(DimacsToken::Quantifier(QuantifierKind::Forall))
        );
        assert_eq!(
            stream.next(),
            Ok(DimacsToken::Quantifier(QuantifierKind::Henkin))
        );
        assert_eq!(stream.next(), Ok(DimacsToken::EOL));

        assert_eq!(stream.next(), Ok(DimacsToken::Literal((-1).into())));
        assert_eq!(stream.next(), Ok(DimacsToken::Literal(1.into())));
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
        assert!(parse_matrix(&mut lexer, &mut matrix, current).is_ok());
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
}
