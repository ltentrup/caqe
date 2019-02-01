use std::ops;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub struct Variable(u32);

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
pub struct Literal {
    x: u32,
}

impl Into<u32> for Variable {
    fn into(self) -> u32 {
        self.0
    }
}
impl Into<u32> for &Variable {
    fn into(self) -> u32 {
        self.0
    }
}

impl Into<usize> for Variable {
    fn into(self) -> usize {
        self.0 as usize
    }
}

impl From<u32> for Variable {
    fn from(val: u32) -> Self {
        Variable(val)
    }
}
impl From<usize> for Variable {
    fn from(val: usize) -> Self {
        Variable(val as u32)
    }
}

impl Literal {
    pub fn new<V: Into<Variable>>(variable: V, signed: bool) -> Literal {
        let variable = variable.into();
        Literal {
            x: variable.0 << 1 | (signed as u32),
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
        Variable(self.x >> 1)
    }

    pub fn dimacs(&self) -> i32 {
        let base = self.variable().0 as i32;
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
        let abs = Variable(literal.abs() as u32);
        Literal::new(abs, signed)
    }
}

impl std::fmt::Debug for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "Literal({})", self.dimacs())
    }
}

impl std::fmt::Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.0)
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
