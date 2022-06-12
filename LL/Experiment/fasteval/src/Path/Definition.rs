
// use core::ops::BitOr;
// use std::marker::Sized;

pub trait IsPath<WordType>
{
    fn push(&mut self, bits: WordType, bit_length: usize) -> ();
}



