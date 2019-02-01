pub mod dimacs;
pub mod dqdimacs;
pub mod qcir;
pub mod qdimacs;

use super::*;
use std::error::Error;
use std::str::Chars;

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
    fn description(&self) -> &str {
        self.msg.as_str()
    }

    fn cause(&self) -> Option<&Error> {
        Some(self)
    }
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
            chars: chars,
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

    fn next_or_error(&mut self) -> Result<char, ParseError> {
        if let Some(c) = self.next() {
            Ok(c)
        } else {
            Err(ParseError {
                msg: format!("Unexpected End-of-File"),
                pos: self.pos,
            })
        }
    }

    fn peek(&self) -> &Option<char> {
        &self.next_char
    }

    fn peek_or_error(&self) -> Result<&char, ParseError> {
        if let Some(c) = self.peek() {
            Ok(c)
        } else {
            Err(ParseError {
                msg: format!("Unexpected End-of-File"),
                pos: self.pos,
            })
        }
    }

    fn read_number(&mut self, first: char) -> Result<u32, ParseError> {
        let mut val = first
            .to_digit(10)
            .expect("internal error, character has to be digit");
        while let Some(digit) = self
            .consume_if(|c| c.is_ascii_digit())
            .and_then(|c| c.to_digit(10))
        {
            val = val * 10 + digit;
        }
        Ok(val)
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
            return Ok(Literal::new(value, signed));
        } else {
            assert!(first == '-');
            return Err(ParseError {
                msg: format!("Expect digits following `-` character"),
                pos: self.pos,
            });
        }
    }

    fn read_identifier(&mut self, first: char) -> Result<String, ParseError> {
        debug_assert!(first.is_ascii_alphabetic() || first == '_');
        let mut value: String = first.to_string();
        while let Some(c) = self.consume_if(|c| c.is_ascii_alphanumeric() || *c == '_') {
            value.push(c);
        }
        Ok(value)
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

    fn consume_if<P>(&mut self, predicate: P) -> Option<char>
    where
        P: Fn(&char) -> bool,
    {
        let c = match self.peek() {
            None => return None,
            Some(c) => *c,
        };
        if predicate(&c) {
            self.next();
            Some(c)
        } else {
            None
        }
    }
}
