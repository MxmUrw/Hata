
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


pub struct Shift0NodeKind();

impl IsNodeKind for Shift0NodeKind
{
    fn slice_shift() -> usize
    {
        0
    }
}


pub struct Shift1NodeKind();

impl IsNodeKind for Shift1NodeKind
{
    fn slice_shift() -> usize
    {
        1
    }
}



