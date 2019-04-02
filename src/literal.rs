use rustc_hash::FxHashMap;
use std::ops;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub struct Variable(u32);

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
pub struct Literal {
    x: u32,
}

#[derive(PartialEq, Eq, Clone)]
pub struct Assignment(FxHashMap<Variable, bool>);

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
        Self(val)
    }
}
impl From<usize> for Variable {
    fn from(val: usize) -> Self {
        #[allow(clippy::cast_possible_truncation)]
        Self(val as u32)
    }
}

impl Literal {
    pub fn new<V: Into<Variable>>(variable: V, signed: bool) -> Self {
        let variable = variable.into();
        Self {
            x: variable.0 << 1 | (signed as u32),
        }
    }

    /// Returns true if `Literal` is signed
    ///
    /// # Examples
    ///
    /// ```
    /// assert!(caqe::Literal::new(0_u32, true).signed());
    /// assert!(!caqe::Literal::new(0_u32, false).signed());
    /// ```
    pub fn signed(self) -> bool {
        (self.x & 1) != 0
    }

    pub fn unsigned(self) -> Self {
        Self { x: self.x & !1 }
    }

    pub fn variable(self) -> Variable {
        Variable(self.x >> 1)
    }

    pub fn dimacs(self) -> i32 {
        #[allow(clippy::cast_possible_wrap)]
        let base = self.variable().0 as i32;
        if self.signed() {
            -base
        } else {
            base
        }
    }
}

impl ops::Neg for Literal {
    type Output = Self;

    fn neg(self) -> Self {
        Self { x: self.x ^ 1 }
    }
}

impl From<i32> for Literal {
    fn from(literal: i32) -> Self {
        let signed = literal < 0;
        #[allow(clippy::cast_sign_loss)]
        let abs = Variable(literal.abs() as u32);
        Self::new(abs, signed)
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

impl Assignment {
    pub(crate) fn hamming(&self, other: &Self) -> u32 {
        let mut count = 0;
        for (var, &val) in &self.0 {
            if other.0[var] != val {
                count += 1;
            }
        }
        count
    }
}

impl From<FxHashMap<Variable, bool>> for Assignment {
    fn from(map: FxHashMap<Variable, bool>) -> Self {
        Self(map)
    }
}

impl std::fmt::Debug for Assignment {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        for (var, val) in &self.0 {
            let x = Literal::new(*var, !val);
            write!(f, "{} ", x.dimacs())?;
        }
        Ok(())
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
