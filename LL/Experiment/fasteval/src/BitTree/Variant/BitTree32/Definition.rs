
use crate::BitTree::Definition::*;

use std::string::*;
use std::fmt;
use std::vec::*;
use std::collections::HashMap;
use std::hash::Hash;

/// A single bit-tree.
///
/// Layout:
/// 1
/// 2 3
/// 4 5 6 7
/// 8 ... 15
/// 16 ... 31
///
pub struct BitTree32
{
    pub bits: u32
}

impl BitTree32
{

}

impl IsBitTree for BitTree32
{
    fn full_height() -> usize
    {
        5
    }

    fn slice_height() -> usize
    {
        4
    }
}


