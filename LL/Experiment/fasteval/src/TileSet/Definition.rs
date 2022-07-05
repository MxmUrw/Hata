
use crate::BitTree::Definition::*;
use crate::Tile::Definition::*;
use crate::Path::Definition::*;
use crate::Path::Wrapper::PathToTile::*;

use std::collections::HashMap;
use std::marker::PhantomData;


pub struct TileSet1<T,BT,P,W,NKG1> where
    T : IsTile<BT,P,W,NKG1>,
    BT : IsBitTree,
    P : IsPath<W>,
    W : IsPathUnit,
{
    pub tiles1: HashMap<PathToTile<BT,P,W>,T>,

    // phantoms
    // pub phantomBT : PhantomData<BT>,
    // pub phantomW : PhantomData<W>,
    pub phantomNKG1 : PhantomData<NKG1>,
}




