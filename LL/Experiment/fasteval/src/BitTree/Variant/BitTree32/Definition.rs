use crate::BitTree::Definition::*;
use crate::Node::NodeKind::Definition::*;
use crate::Path::Definition::*;
use crate::Path::Wrapper::PathInTile::*;

use std::collections::HashMap;
use std::fmt;
use std::hash::Hash;
use std::ops::BitOr;
use std::string::*;
use std::vec::*;

/// A single bit-tree.
///
/// Layout:
/// 1
/// 2 3
/// 4 5 6 7
/// 8 ... 15
/// 16 ... 31
///
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct BitTree32
{
    pub bits: u32,
}

impl BitTree32
{
    fn get_index<P, W>(p_immut: &P) -> usize
    where
        P: IsPath<W>,
        W: IsPathUnit,
    {
        let mut p = p_immut.clone();
        let mut index = 1usize;
        while p.length() > 0
        {
            let direction = p.pop_at_root_bit();
            index = index * 2 + (direction as usize);
        }
        index
    }
}

impl BitOr for BitTree32
{
    type Output = BitTree32;
    fn bitor(self, other: BitTree32) -> BitTree32
    {
        BitTree32 {
            bits: self.bits | other.bits,
        }
    }
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

    fn from<NK: IsNodeKind, P: IsPath<W>, W: IsPathUnit>(
        path: PathInTile<Self, P, W, NK>,
    ) -> BitTree32
    {
        println!("Have the following path: {}", path.0);
        let p = path.0;
        let index = BitTree32::get_index(&p);
        let tree = 1 << index;

        let res = BitTree32 { bits: tree };
        println!("The tree is: ");
        println!("{res}");
        res
    }
    fn empty() -> BitTree32
    {
        BitTree32 { bits: 0 }
    }

    fn get_bit<P, W>(&self, p: &P) -> bool
    where
        P: IsPath<W>,
        W: IsPathUnit,
    {
        let i = BitTree32::get_index(p);
        let value_at_i = (self.bits >> i) & 1;
        value_at_i != 0
    }
}
