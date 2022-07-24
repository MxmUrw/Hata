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

type MyTileSet<P, W> = TileSet1<LamAppTile<BitTree32, P, W>, BitTree32, P, W, LamAppNKG<P>>;

pub fn decode<Path, W>(ts: &MyTileSet<Path, W>) -> TreeTerm
where
    Path: IsPath<W>,
    W: IsPathUnit + Clone,
{
    decode_impl(ts, &HashMap::new(), 0, &Path::root())
}

pub fn decode_impl<Path, W>(ts: &MyTileSet<Path, W>, current_vars: &HashMap<Path,String>, current_var: usize, current_path: &Path) -> TreeTerm
where
    Path: IsPath<W>,
    W: IsPathUnit + Clone,
{
    if let Some(nk) = ts.get_node_kind(current_path)
    {
        match nk
        {
            LamAppNKG::Lam(rel_var_paths) =>
            {
                let mut path_l = current_path.clone();
                path_l.push_at_leaf(W::left(),1);

                // create new var paths
                let varname = format!("v{current_var}");
                let mut newvars = current_vars.clone();
                for rel_var_path in rel_var_paths
                {
                    let mut path = current_path.clone();
                    path.join_at_leaf(rel_var_path);
                    println!("Adding path {path} at {current_path}");
                    newvars.insert(path, varname.clone());
                }
                let tree_l = decode_impl(ts, &newvars, current_var + 1, &path_l);

                TreeTerm::Λ(varname, Box::new(tree_l))
            }
            LamAppNKG::App =>
            {
                let mut path_l = current_path.clone();
                path_l.push_at_leaf(W::left(),1);
                let tree_l = decode_impl(ts, current_vars, current_var, &path_l);

                let mut path_r = current_path.clone();
                path_r.push_at_leaf(W::right(),1);
                let tree_r = decode_impl(ts, current_vars, current_var, &path_r);

                TreeTerm::App(Box::new(tree_l), Box::new(tree_r))
            }
        }
    }
    else if let Some(varname) = current_vars.get(current_path)
    {
        TreeTerm::Var(varname.clone())
    }
    else
    {
        TreeTerm::Invalid()
    }
}
