/// This trait describes objects that can be repesented as
/// (a possible extension) of the DIMACS file format.
pub trait Dimacs {
    fn dimacs(&self) -> String;
}
