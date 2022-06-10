
use core::ops::BitOr;
use std::marker::Sized;

trait IsPath: BitOr + Sized
{
    fn push(&mut self, bits: u32, bit_length: usize) -> ();
}



