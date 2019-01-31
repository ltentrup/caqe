use std::ops;

pub type Variable = u32;

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
pub struct Literal {
    x: u32,
}

impl Literal {
    pub fn new(variable: Variable, signed: bool) -> Literal {
        Literal {
            x: variable << 1 | (signed as u32),
        }
    }

    /// Returns true if `Literal` is signed
    ///
    /// # Examples
    ///
    /// ```
    /// assert!(caqe::Literal::new(0, true).signed());
    /// assert!(!caqe::Literal::new(0, false).signed());
    /// ```
    pub fn signed(&self) -> bool {
        (self.x & 1) != 0
    }

    pub fn unsigned(&self) -> Literal {
        Literal { x: self.x & !1 }
    }

    pub fn variable(&self) -> Variable {
        self.x >> 1
    }

    pub fn dimacs(&self) -> i32 {
        let base = self.variable() as i32;
        if self.signed() {
            -base
        } else {
            base
        }
    }
}

impl ops::Neg for Literal {
    type Output = Literal;

    fn neg(self) -> Literal {
        Literal { x: self.x ^ 1 }
    }
}

impl From<i32> for Literal {
    fn from(literal: i32) -> Self {
        let signed = literal < 0;
        let abs = literal.abs() as Variable;
        Literal::new(abs, signed)
    }
}

impl std::fmt::Debug for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "Literal({})", self.dimacs())
    }
}

#[cfg(test)]
mod tests {

    use std::mem;

    use super::*;

    #[test]
    fn size_of_literal() {
        let result = mem::size_of::<Literal>();
        assert!(
            result == 4,
            "Size of `Literal` should be 4 bytes, was `{}`",
            result
        );
    }
}
