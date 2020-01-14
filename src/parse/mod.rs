pub mod dimacs;
pub mod dqdimacs;
pub mod qdimacs;

use super::*;
use std::error::Error;
use std::str::Chars;

#[allow(clippy::module_name_repetitions)]
#[derive(Debug, Eq, PartialEq)]
pub struct ParseError {
    pub msg: String,
    pub pos: SourcePos,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "parse error: {} at {}", self.description(), self.pos)
    }
}

impl Error for ParseError {
    #[must_use]
    fn description(&self) -> &str {
        self.msg.as_str()
    }

    #[must_use]
    fn cause(&self) -> Option<&dyn Error> {
        Some(self)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct SourcePos {
    line: usize,
    column: usize,
}

impl SourcePos {
    fn new() -> Self {
        Self { line: 0, column: 0 }
    }

    fn advance(&mut self, len: usize) {
        self.column += len;
    }

    fn newline(&mut self) {
        self.line += 1;
        self.column = 0;
    }
}

impl std::fmt::Display for SourcePos {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

struct CharIterator<'a> {
    chars: Chars<'a>,
    pos: SourcePos,
    next_char: Option<char>,
}

impl<'a> CharIterator<'a> {
    fn new(content: &'a str) -> CharIterator<'a> {
        let mut chars = content.chars();
        CharIterator {
            next_char: chars.next(),
            chars,
            pos: SourcePos::new(),
        }
    }

    fn next(&mut self) -> Option<char> {
        match self.next_char {
            None => None,
            Some(c) => {
                if c == '\n' {
                    self.pos.newline()
                } else {
                    self.pos.advance(1)
                }
                self.next_char = self.chars.next();
                Some(c)
            }
        }
    }

    fn read_literal(&mut self, first: char) -> Result<Literal, ParseError> {
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
            Ok(Literal::new(value, signed))
        } else {
            assert!(first == '-');
            Err(ParseError {
                msg: "Expect digits following `-` character".to_string(),
                pos: self.pos,
            })
        }
    }

    fn expect_char(&mut self, expected: char) -> Result<(), ParseError> {
        match self.next() {
            None => Err(ParseError {
                msg: "Unexpected end of input".to_string(),
                pos: self.pos,
            }),
            Some(c) => {
                if c == expected {
                    Ok(())
                } else {
                    Err(ParseError {
                        msg: format!("Expected character `{}`, but found `{}`", expected, c),
                        pos: self.pos,
                    })
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
