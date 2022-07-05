

use crate::Path::Definition::*;
use crate::Node::NodeKind::Definition::*;
use crate::BitTree::Definition::*;

use std::marker::PhantomData;


// TODO: This currently requires BT and W to have Eq, Hash implementations
// But they are not really necessary since they are only phantom data.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PathToTile<BT,P,W>(pub P, PhantomData<(BT,W)>) where
    BT: IsBitTree,
    P: IsPath<W>,
    W: IsPathUnit;


impl<BT,P,W> PathToTile<BT,P,W> where
    BT: IsBitTree,
    P: IsPath<W>,
    W: IsPathUnit
{
    pub fn new(p: P) -> Self
    {
        // make sure that our path has the correct length
        // for a path to a tile, the following must hold:
        assert_eq!(p.length() % BT::slice_height(), 0);

        PathToTile(p, PhantomData)
    }
}




