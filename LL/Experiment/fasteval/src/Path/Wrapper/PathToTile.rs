

use crate::Path::Definition::*;
use crate::NodeKind::Definition::*;
use crate::BitTree::Definition::*;

use std::marker::PhantomData;


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




