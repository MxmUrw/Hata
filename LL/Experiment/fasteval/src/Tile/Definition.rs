
use crate::Path::Definition::*;
use crate::BitTree::Definition::*;

use std::marker::PhantomData;


pub struct Tile<BT> where
    BT : IsBitTree,
    // P : IsPath<W>,
    // W : IsPathUnit
{
    // path : P,
    tree_λ : BT,
    tree_app : BT,

    // phantoms
    // phantom : PhantomData<W>,
}

// impl<BT,P,W> Tile<BT,P,W> where
impl<BT> Tile<BT> where
    BT : IsBitTree,
    // P : IsPath<W>,
    // W : IsPathUnit
{
    // pub fn new_single_λ(_p: &P) -> Self
    // {
    //     todo!()
    // }
}



