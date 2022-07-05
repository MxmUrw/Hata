
// use core::ops::BitOr;
// use std::marker::Sized;

use std::fmt::Display;

pub trait IsPathUnit :
  Eq + std::hash::Hash
{
    fn left() -> Self;
    fn right() -> Self;
}

pub trait IsPath<PathUnit> :
    Display + Clone + Eq + std::hash::Hash
where
    PathUnit : IsPathUnit
{
    fn root() -> Self;
    fn push_at_leaf(&mut self, bits: PathUnit, bit_length: usize);
    fn pop_at_leaf(&mut self, bit_length: usize) -> Self;
    fn length(&self) -> usize;
}



