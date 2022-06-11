
// use super::path_old::*;
use bitvec::prelude::*;

/// A path of generic size.
pub struct Path<const N: usize>
{
    bits: BitArray<[u32; N]>,

    /// The actual number of bits that the path uses.
    /// This has to be <= 32*N of course.
    path_length: usize
}



