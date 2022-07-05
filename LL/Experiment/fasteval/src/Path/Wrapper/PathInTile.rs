

use crate::Path::Definition::*;
use crate::Node::NodeKind::Definition::*;
use crate::BitTree::Definition::*;

use std::marker::PhantomData;
use more_asserts::*;

pub struct PathInTile<BT,P,W,NK>(pub P, PhantomData<(BT,W,NK)>) where
    BT: IsBitTree,
    P: IsPath<W>,
    W: IsPathUnit,
    NK: IsNodeKind;


impl<BT,P,W,NK> PathInTile<BT,P,W,NK> where
    BT: IsBitTree,
    P: IsPath<W>,
    W: IsPathUnit,
    NK: IsNodeKind
{
    pub fn new(p: P) -> Self
    {
        println!("Constructing path in tile for {p}");
        // make sure that our path has the correct length
        // for paths in tiles, it must hold that
        // p.length ∈ [slice_shift .. slice_height+slice_shift]
        debug_assert_le!(NK::slice_shift(),p.length());
        debug_assert_lt!(p.length(), BT::slice_height() + NK::slice_shift());

        PathInTile(p, PhantomData)
    }
}


