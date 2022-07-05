
use crate::BitTree::Definition::*;
use crate::Tile::Definition::*;
use crate::Path::Definition::*;

use std::collections::HashMap;
use std::marker::PhantomData;


pub struct TileSet<BT,P,W> where
    BT : IsBitTree,
    P : IsPath<W>,
    W : IsPathUnit,
{
    tiles: HashMap<P,Tile<BT>>,

    // phantoms
    phantom : PhantomData<W>,
}




