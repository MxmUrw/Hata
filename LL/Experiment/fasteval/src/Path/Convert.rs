
use crate::BitTree::Definition::*;
use crate::NodeKind::Definition::*;
use crate::Path::Definition::*;
use crate::Path::Wrapper::PathInTile::*;
use crate::Path::Wrapper::PathToTile::*;


pub fn split_raw_path<BT,P,W,NK>(p : &P) -> (PathInTile<BT,P,W,NK>, PathToTile<BT,P,W>) where
    BT : IsBitTree,
    P : IsPath<W>,
    W : IsPathUnit,
    NK : IsNodeKind
{
    let l = p.length();
    let mut path_in_tile_length = l % BT::slice_height();
    if path_in_tile_length < NK::slice_shift()
    {
        path_in_tile_length += BT::slice_height();
    }

    todo!()
}






