use std::collections::HashMap;
use std::hash::*;

use crate::AlgebraLL::MutMonoid::Definition::*;
use crate::BitTree::Variant::BitTree32::Definition::*;
use crate::Node::NodeKindGroup::Example::LamAppNKG::*;
use crate::NodePath::Definition::*;
use crate::Path::Definition::*;
use crate::Term::Tree::Definition::*;
use crate::Tile::Example::LamAppTile::*;
use crate::TileSet::Definition::*;
use crate::TileSet::Instance::MutMonoid::*;

type MyTileSet<P, W> = TileSet1<LamAppTile<BitTree32>, BitTree32, P, W, LamAppNKG>;

pub fn decode<Path, W>(ts: &MyTileSet<Path, W>) -> TreeTerm
where
    Path: IsPath<W>,
    W: IsPathUnit + Clone,
{
    decode_impl(ts, &Path::root())
}

pub fn decode_impl<Path, W>(ts: &MyTileSet<Path, W>, current_path: &Path) -> TreeTerm
where
    Path: IsPath<W>,
    W: IsPathUnit + Clone,
{
    if let Some(nk) = ts.get_node_kind(current_path)
    {
        match nk
        {
            LamAppNKG::Lam =>
            {
                let mut path_l = current_path.clone();
                path_l.push_at_leaf(W::left(),1);
                let tree_l = decode_impl(ts, &path_l);

                TreeTerm::Λ("v".to_string(), Box::new(tree_l))
            }
            LamAppNKG::App =>
            {
                let mut path_l = current_path.clone();
                path_l.push_at_leaf(W::left(),1);
                let tree_l = decode_impl(ts, &path_l);

                let mut path_r = current_path.clone();
                path_r.push_at_leaf(W::right(),1);
                let tree_r = decode_impl(ts, &path_r);

                TreeTerm::App(Box::new(tree_l), Box::new(tree_r))
            }
        }
    }
    else
    {
        TreeTerm::Invalid()
    }
}
