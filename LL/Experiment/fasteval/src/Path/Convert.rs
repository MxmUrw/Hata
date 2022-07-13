use crate::BitTree::Definition::*;
use crate::Node::NodeKind::Definition::*;
use crate::Path::Definition::*;
use crate::Path::Wrapper::PathInTile::*;
use crate::Path::Wrapper::PathToTile::*;

pub fn split_raw_path<BT, P, W, NK>(p: &P) -> (PathToTile<BT, P, W>, PathInTile<BT, P, W, NK>)
where
    BT: IsBitTree,
    P: IsPath<W>,
    W: IsPathUnit,
    NK: IsNodeKind,
{
    let l = p.length();
    let mut path_in_tile_length = l % BT::slice_height();
    if path_in_tile_length < NK::slice_shift()
    {
        path_in_tile_length += BT::slice_height();
    }
    // if l < path_in_tile_length
    // this means that we are in tile 0,
    // and our path should be shifted to "tile -1".
    // since that doesn't exist, we let the path be in this
    // tile.
    let (path_to_tile_length, bAllowAllPaths) = if l < path_in_tile_length
    {
        (0, true)
    }
    else
    {
        (l - path_in_tile_length, false)
    };

    // let path_to_tile_length = l - path_in_tile_length;
    let mut path = p.clone();
    let path_to_tile = path.pop_at_root(path_to_tile_length);
    let path_in_tile = path;

    // println!("Splitting path: {p}\npath_in_tile_length: {path_in_tile_length}\npath_to_tile: {path_to_tile}\npath_in_tile: {path_in_tile}");
    // println!("Slice_shift: {}", NK::slice_shift());
    // println!(" => where bits: {}, length: {}", path_in_tile.0, path_in_tile.1);

    (
        PathToTile::new(path_to_tile),
        PathInTile::new(path_in_tile, bAllowAllPaths),
    )
}

pub fn split_raw_path_nk01<BT, P, W>(p: &P) -> Vec<(PathToTile<BT, P, W>, P)>
where
    BT: IsBitTree,
    P: IsPath<W>,
    W: IsPathUnit,
{
    let (p0, rp0) = split_raw_path::<_, _, _, Shift0NodeKind>(p);
    let (p1, rp1) = split_raw_path::<_, _, _, Shift1NodeKind>(p);
    vec![(p0, rp0.0), (p1, rp1.0)]
}
