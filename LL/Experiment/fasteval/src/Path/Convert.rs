
use crate::BitTree::Definition::*;
use crate::NodeKind::Definition::*;
use crate::Path::Definition::*;
use crate::Path::Wrapper::PathInTile::*;
use crate::Path::Wrapper::PathToTile::*;


pub fn split_raw_path<BT,P,W,NK>(p : &P) -> (PathToTile<BT,P,W>, PathInTile<BT,P,W,NK>) where
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
    let mut path_to_tile = p.clone();
    let path_in_tile = path_to_tile.pop_at_leaf(path_in_tile_length);

    println!("Splitting path: {p}\npath_in_tile_length: {path_in_tile_length}\npath_to_tile: {path_to_tile}\npath_in_tile: {path_in_tile}");

    (PathToTile::new(path_to_tile), PathInTile::new(path_in_tile))
}




