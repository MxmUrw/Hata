
// use core::ops::BitOr;
// use std::marker::Sized;

use std::fmt::Display;

pub trait IsPathUnit
{
    fn left() -> Self;
    fn right() -> Self;
}

pub trait IsPath<PathUnit> :
    Display + Clone
where
    PathUnit : IsPathUnit
{
    fn root() -> Self;
    fn push(&mut self, bits: PathUnit, bit_length: usize);
}



