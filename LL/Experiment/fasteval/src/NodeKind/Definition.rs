
use crate::Path::Definition::*;
use crate::BitTree::Definition::*;


// trait IsNodeKind<BT,P,W> where
    // BT: IsBitTree,
    // P: IsPath<W>,
    // W: IsPathUnit
pub trait IsNodeKind
{
    fn slice_shift() -> usize;
}


