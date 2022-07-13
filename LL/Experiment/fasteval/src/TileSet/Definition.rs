use crate::BitTree::Definition::*;
use crate::Node::NodeKind::Definition::*;
use crate::Path::Convert::*;
use crate::Path::Definition::*;
use crate::Path::Wrapper::PathInTile::*;
use crate::Path::Wrapper::PathToTile::*;
use crate::Tile::Definition::*;

use std::collections::HashMap;
use std::marker::PhantomData;

////////////////////////////////////////
// The generic trait

pub trait IsTileSetFor<T, BT, P, W, NKG>
where
    T: IsTile<BT, P, W, NKG>,
    BT: IsBitTree,
    P: IsPath<W>,
    W: IsPathUnit,
{
    fn get_node_kind(&self, p: &P) -> Option<NKG>;
}

////////////////////////////////////////
// The implementation for a single kind of tiles

pub struct TileSet1<T, BT, P, W, NKG1>
where
    T: IsTile<BT, P, W, NKG1>,
    BT: IsBitTree,
    P: IsPath<W>,
    W: IsPathUnit,
{
    pub tiles1: HashMap<PathToTile<BT, P, W>, T>,

    // phantoms
    // pub phantomBT : PhantomData<BT>,
    // pub phantomW : PhantomData<W>,
    pub phantomNKG1: PhantomData<NKG1>,
}

impl<T, BT, P, W, NKG1> IsTileSetFor<T, BT, P, W, NKG1> for TileSet1<T, BT, P, W, NKG1>
where
    T: IsTile<BT, P, W, NKG1>,
    BT: IsBitTree,
    P: IsPath<W>,
    W: IsPathUnit,
{
    fn get_node_kind(&self, p: &P) -> Option<NKG1>
    {
        let pathpairs = split_raw_path_nk01::<BT, P, W>(p);
        for (p, rp) in &pathpairs
        {
            if let Some(tile) = self.tiles1.get(p)
            {
                if let Some(nkg) = tile.get(rp)
                {
                    return Some(nkg);
                }
            }
        }
        return None;
    }
}

//////////////////////////////////////
// helpers

// pub fn split_raw_path<BT, P, W, NK>(p: &P) -> (PathToTile<BT, P, W>, PathInTile<BT, P, W, NK>)
// where
//     BT: IsBitTree,
//     P: IsPath<W>,
//     W: IsPathUnit,
//     NK: IsNodeKind,
// {
//     todo!()
// }
