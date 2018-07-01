use super::super::*;
use super::{CharIterator, ParseError, SourcePos};
use std::collections::HashMap;

#[derive(Debug, Eq, PartialEq)]
pub enum QCIRQuantKind {
    Exists,
    Forall,
}

#[derive(Debug, Eq, PartialEq)]
pub enum GateKind {
    And,
    Or,
    Xor,
    Ite,
}

#[derive(Debug, Eq, PartialEq)]
pub enum QCIRToken {
    /// QCIR header
    Header,

    /// An identifier, can be variable or gate name
    Ident(SymbolId),

    /// Negation sign `-`
    Negation,

    /// number, representing variables and gates in cleansed format
    Number(u32),

    /// Quantification, i.e., `exists` and `forall`
    Quant(QCIRQuantKind),

    /// Free quantifier block
    Free,

    /// The circuit output
    Output,

    /// a gate, i.e., `and`, `or`
    Gate(GateKind),

    Xor,

    Ite,

    /// Opening parenthesis `(`
    LPar,

    /// Closing parenthesis `)`
    RPar,

    /// Comma `,`
    Comma,

    /// Semicolon `;`
    Semicolon,

    /// Equal sign `=`
    Equal,

    /// End-of-file
    EOF,
}

type SymbolId = u32;

struct QCIRLexer<'a> {
    chars: CharIterator<'a>,
    symboltable: HashMap<String, SymbolId>,
}

impl<'a> QCIRLexer<'a> {
    fn new(content: &'a str) -> QCIRLexer<'a> {
        QCIRLexer {
            chars: CharIterator::new(content),
            symboltable: HashMap::new(),
        }
    }

    pub fn next(&mut self) -> Result<QCIRToken, ParseError> {
        while let Some(c) = self.chars.next() {
            match c {
                '#' => {
                    // comment line or QCIR header
                    match self.chars.next_or_error()? {
                        'Q' => {
                            // expect #QCIR header
                            self.chars.expect_str("CIR-G14")?;
                            return Ok(QCIRToken::Header);
                        }
                        '\n' => {
                            // empty comment line
                            continue;
                        }
                        _ => {
                            // comment line, ignore until next newline
                            self.chars.skip_while(|c| *c != '\n');
                        }
                    }
                }
                '-' => return Ok(QCIRToken::Negation),
                '(' => return Ok(QCIRToken::LPar),
                ')' => return Ok(QCIRToken::RPar),
                ',' => return Ok(QCIRToken::Comma),
                ';' => return Ok(QCIRToken::Semicolon),
                '=' => return Ok(QCIRToken::Equal),
                c if c.is_ascii_digit() => {
                    // read unsigned number
                    return Ok(QCIRToken::Number(self.chars.read_number(c)?));
                }
                c if c.is_ascii_whitespace() => continue,
                c if c.is_ascii_alphabetic() || c == '_' => {
                    // identifier, containing letters, digits, and underscores
                    let identifier = self.chars.read_identifier(c)?;
                    return Ok(self.process_identifier(identifier));
                }
                _ => {
                    return Err(ParseError {
                        msg: format!("Encountered unknown token `{}` during lexing", c),
                        pos: self.chars.pos,
                    })
                }
            }
        }
        // end of file
        return Ok(QCIRToken::EOF);
    }

    fn process_identifier(&mut self, ident: String) -> QCIRToken {
        match ident.to_ascii_lowercase().as_ref() {
            "forall" => QCIRToken::Quant(QCIRQuantKind::Forall),
            "exists" => QCIRToken::Quant(QCIRQuantKind::Exists),
            "free" => QCIRToken::Free,
            "output" => QCIRToken::Output,
            "and" => QCIRToken::Gate(GateKind::And),
            "or" => QCIRToken::Gate(GateKind::Or),
            "xor" => QCIRToken::Gate(GateKind::Xor),
            "ite" => QCIRToken::Gate(GateKind::Ite),
            _ => {
                let len = self.symboltable.len() as SymbolId;
                let entry = self.symboltable.entry(ident).or_insert(len);
                QCIRToken::Ident(*entry)
            }
        }
    }

    fn pos(&self) -> SourcePos {
        self.chars.pos
    }

    fn expect_next_token(&mut self, token: QCIRToken) -> Result<(), ParseError> {
        let next = self.next()?;
        if next != token {
            Err(ParseError {
                msg: format!("Expect token `{:?}` but found {:?}", token, next),
                pos: self.pos(),
            })
        } else {
            Ok(())
        }
    }
}

fn parse(lexer: &mut QCIRLexer) -> Result<(), ParseError> {
    // first token has to be `#QCIR-G14` header
    let first = lexer.next()?;
    if first != QCIRToken::Header {
        return Err(ParseError {
            msg: format!("Expect `#QCIR-G14` header, but found `{:?}`", first),
            pos: lexer.pos(),
        });
    }
    // next token is
    // (1) either an integer, representing the maximal number of identifier (and guaranteing cleansed format)
    // (2) or the start of the quantifier prefix
    let is_cleansed;
    let token = match lexer.next()? {
        QCIRToken::Number(val) => {
            is_cleansed = true;
            lexer.next()?
        }
        token => {
            is_cleansed = false;
            token
        }
    };
    let token = parse_free_variables(lexer, token)?;
    let token = parse_quantifier(lexer, token)?;
    let token = parse_output(lexer, token)?;
    parse_gates(lexer)?;
    Ok(())
}

fn parse_free_variables(lexer: &mut QCIRLexer, token: QCIRToken) -> Result<QCIRToken, ParseError> {
    Ok(match token {
        QCIRToken::Free => {
            parse_var_list(lexer, |symbol| {})?;
            lexer.next()?
        }
        t => t,
    })
}

fn parse_quantifier(lexer: &mut QCIRLexer, mut token: QCIRToken) -> Result<QCIRToken, ParseError> {
    let next = loop {
        match token {
            QCIRToken::Quant(qtype) => {
                parse_var_list(lexer, |symbol| {})?;
                token = lexer.next()?
            }
            t => break t,
        }
    };
    Ok(next)
}

fn parse_output(lexer: &mut QCIRLexer, token: QCIRToken) -> Result<(), ParseError> {
    Ok(match token {
        QCIRToken::Output => {
            lexer.expect_next_token(QCIRToken::LPar)?;
            let next = lexer.next()?;
            parse_lit(lexer, next)?;
            lexer.expect_next_token(QCIRToken::RPar)?;
        }
        t => {
            return Err(ParseError {
                msg: format!("Expect token `{:?}` but found {:?}", QCIRToken::Output, t),
                pos: lexer.pos(),
            })
        }
    })
}

/// Parses lists of variables, seperated by `,` and returns the following token
fn parse_var_list<F>(lexer: &mut QCIRLexer, on_var: F) -> Result<(), ParseError>
where
    F: Fn(SymbolId) -> (),
{
    lexer.expect_next_token(QCIRToken::LPar)?;
    let end = loop {
        match lexer.next()? {
            QCIRToken::Ident(i) => {
                // identifier
                on_var(i);
                match lexer.next()? {
                    QCIRToken::Comma => continue,
                    t => break t,
                }
            }
            t => break t,
        }
    };
    if end != QCIRToken::RPar {
        Err(ParseError {
            msg: format!("Expect token `{:?}` but found {:?}", QCIRToken::RPar, end),
            pos: lexer.pos(),
        })
    } else {
        Ok(())
    }
}

/// Parses potentially negated literals
fn parse_lit(lexer: &mut QCIRLexer, token: QCIRToken) -> Result<Literal, ParseError> {
    match token {
        QCIRToken::Negation => match lexer.next()? {
            QCIRToken::Ident(name) => return Ok(Literal::new(name, true)),
            t => {
                return Err(ParseError {
                    msg: format!("Expect identifier but found {:?}", t),
                    pos: lexer.pos(),
                })
            }
        },
        QCIRToken::Ident(name) => return Ok(Literal::new(name, false)),
        t => {
            return Err(ParseError {
                msg: format!("Expect identifier but found {:?}", t),
                pos: lexer.pos(),
            })
        }
    }
}

/// Parses lists of literals, seperated by `,` and returns the following token
fn parse_lit_list<F>(
    lexer: &mut QCIRLexer,
    on_lit: F,
    end_token: QCIRToken,
) -> Result<(), ParseError>
where
    F: Fn(Literal) -> (),
{
    lexer.expect_next_token(QCIRToken::LPar)?;
    let end = loop {
        match lexer.next()? {
            QCIRToken::Negation => {
                // negated identifier
                on_lit(parse_lit(lexer, QCIRToken::Negation)?);
                match lexer.next()? {
                    QCIRToken::Comma => continue,
                    t => break t,
                }
            }
            QCIRToken::Ident(i) => {
                // identifier
                on_lit(parse_lit(lexer, QCIRToken::Ident(i))?);
                match lexer.next()? {
                    QCIRToken::Comma => continue,
                    t => break t,
                }
            }
            t => break t,
        }
    };
    if end != end_token {
        Err(ParseError {
            msg: format!("Expect token `{:?}` but found {:?}", end_token, end),
            pos: lexer.pos(),
        })
    } else {
        Ok(())
    }
}

fn parse_gates(lexer: &mut QCIRLexer) -> Result<(), ParseError> {
    Ok(loop {
        match lexer.next()? {
            QCIRToken::Ident(name) => {
                // gate definition is gate = type(var-list)
                lexer.expect_next_token(QCIRToken::Equal)?;
                match lexer.next()? {
                    QCIRToken::Gate(gtype) => {
                        parse_lit_list(lexer, |lit| {}, QCIRToken::RPar)?;
                    }
                    QCIRToken::Xor => {
                        // xor(lit, lit)
                        lexer.expect_next_token(QCIRToken::LPar)?;
                        let next_token = lexer.next()?;
                        parse_lit(lexer, next_token)?;
                        lexer.expect_next_token(QCIRToken::Comma)?;
                        let next_token = lexer.next()?;
                        parse_lit(lexer, next_token)?;
                        lexer.expect_next_token(QCIRToken::RPar)?;
                    }
                    QCIRToken::Ite => {
                        // ite(lit, lit, lit)
                        lexer.expect_next_token(QCIRToken::LPar)?;
                        let next_token = lexer.next()?;
                        parse_lit(lexer, next_token)?;
                        lexer.expect_next_token(QCIRToken::Comma)?;
                        let next_token = lexer.next()?;
                        parse_lit(lexer, next_token)?;
                        lexer.expect_next_token(QCIRToken::Comma)?;
                        let next_token = lexer.next()?;
                        parse_lit(lexer, next_token)?;
                        lexer.expect_next_token(QCIRToken::RPar)?;
                    }
                    QCIRToken::Quant(qtype) => {
                        // quant(lit-var; lit)
                        parse_lit_list(lexer, |lit| {}, QCIRToken::Semicolon)?;
                        let next_token = lexer.next()?;
                        parse_lit(lexer, next_token)?;
                        lexer.expect_next_token(QCIRToken::RPar)?;
                    }
                    t => {
                        return Err(ParseError {
                            msg: format!("Expect gate type `and`, `or`, `xor`, `ite`, `forall`, or `exists`, but found token {:?}", t),
                            pos: lexer.pos(),
                        })
                    }
                }
            }
            QCIRToken::EOF => break,
            t => {
                return Err(ParseError {
                    msg: format!("Expect gate definition but found token {:?}", t),
                    pos: lexer.pos(),
                })
            }
        }
    })
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_lexer_simple() {
        let mut lexer = QCIRLexer::new("#QCIR-G14\nforall(v1)\nexists(v2, v3)\noutput(g3)\ng1 = and(v1, v2)\ng2 = and(-v1, -v2, v3)\ng3 = or(g1, g2)\n");

        // #QCIR-G14
        assert_eq!(lexer.next(), Ok(QCIRToken::Header));

        // forall(v1)
        assert_eq!(lexer.next(), Ok(QCIRToken::Quant(QCIRQuantKind::Forall)));
        assert_eq!(lexer.next(), Ok(QCIRToken::LPar));
        assert_eq!(lexer.next(), Ok(QCIRToken::Ident(0)));
        assert_eq!(lexer.next(), Ok(QCIRToken::RPar));

        // exists(v2, v3)
        assert_eq!(lexer.next(), Ok(QCIRToken::Quant(QCIRQuantKind::Exists)));
        assert_eq!(lexer.next(), Ok(QCIRToken::LPar));
        assert_eq!(lexer.next(), Ok(QCIRToken::Ident(1)));
        assert_eq!(lexer.next(), Ok(QCIRToken::Comma));
        assert_eq!(lexer.next(), Ok(QCIRToken::Ident(2)));
        assert_eq!(lexer.next(), Ok(QCIRToken::RPar));

        // output(g3)
        assert_eq!(lexer.next(), Ok(QCIRToken::Output));
        assert_eq!(lexer.next(), Ok(QCIRToken::LPar));
        assert_eq!(lexer.next(), Ok(QCIRToken::Ident(3)));
        assert_eq!(lexer.next(), Ok(QCIRToken::RPar));

        // g1 = and(v1, v2)
        assert_eq!(lexer.next(), Ok(QCIRToken::Ident(4)));
        assert_eq!(lexer.next(), Ok(QCIRToken::Equal));
        assert_eq!(lexer.next(), Ok(QCIRToken::Gate(GateKind::And)));
        assert_eq!(lexer.next(), Ok(QCIRToken::LPar));
        assert_eq!(lexer.next(), Ok(QCIRToken::Ident(0)));
        assert_eq!(lexer.next(), Ok(QCIRToken::Comma));
        assert_eq!(lexer.next(), Ok(QCIRToken::Ident(1)));
        assert_eq!(lexer.next(), Ok(QCIRToken::RPar));

        // g2 = and(-v1, -v2, v3)
        assert_eq!(lexer.next(), Ok(QCIRToken::Ident(5)));
        assert_eq!(lexer.next(), Ok(QCIRToken::Equal));
        assert_eq!(lexer.next(), Ok(QCIRToken::Gate(GateKind::And)));
        assert_eq!(lexer.next(), Ok(QCIRToken::LPar));
        assert_eq!(lexer.next(), Ok(QCIRToken::Negation));
        assert_eq!(lexer.next(), Ok(QCIRToken::Ident(0)));
        assert_eq!(lexer.next(), Ok(QCIRToken::Comma));
        assert_eq!(lexer.next(), Ok(QCIRToken::Negation));
        assert_eq!(lexer.next(), Ok(QCIRToken::Ident(1)));
        assert_eq!(lexer.next(), Ok(QCIRToken::Comma));
        assert_eq!(lexer.next(), Ok(QCIRToken::Ident(2)));
        assert_eq!(lexer.next(), Ok(QCIRToken::RPar));

        // g3 = or(g1, g2)
        assert_eq!(lexer.next(), Ok(QCIRToken::Ident(3)));
        assert_eq!(lexer.next(), Ok(QCIRToken::Equal));
        assert_eq!(lexer.next(), Ok(QCIRToken::Gate(GateKind::Or)));
        assert_eq!(lexer.next(), Ok(QCIRToken::LPar));
        assert_eq!(lexer.next(), Ok(QCIRToken::Ident(4)));
        assert_eq!(lexer.next(), Ok(QCIRToken::Comma));
        assert_eq!(lexer.next(), Ok(QCIRToken::Ident(5)));
        assert_eq!(lexer.next(), Ok(QCIRToken::RPar));

        assert_eq!(lexer.next(), Ok(QCIRToken::EOF));
    }

    #[test]
    fn test_parse_simple() {
        let mut lexer = QCIRLexer::new("#QCIR-G14\nforall(v1)\nexists(v2, v3)\noutput(g3)\ng1 = and(v1, v2)\ng2 = and(-v1, -v2, v3)\ng3 = or(g1, g2)\n");
        assert!(!parse(&mut lexer).is_err());
    }
}
