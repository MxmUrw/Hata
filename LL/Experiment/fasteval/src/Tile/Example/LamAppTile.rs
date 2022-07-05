use crate::BitTree::Definition::*;
use crate::Node::NodeKind::Definition::*;
use crate::Node::NodeKindGroup::Example::LamAppNKG::*;
use crate::NodePath::Definition::*;
use crate::Path::Definition::*;
use crate::Path::Wrapper::PathToTile::*;
use crate::Tile::Definition::*;
use crate::Path::Convert::*;

use std::marker::PhantomData;

pub struct LamAppTile<BT>
where
    BT: IsBitTree,
    // P : IsPath<W>,
    // W : IsPathUnit
{
    // path : P,
    tree_lam: BT,
    tree_app: BT,
}

// impl<BT,P,W> Tile<BT,P,W> where
impl<BT> LamAppTile<BT>
where
    BT: IsBitTree,
    // P : IsPath<W>,
    // W : IsPathUnit
{
    // pub fn new_single_λ(_p: &P) -> Self
    // {
    //     todo!()
    // }
}

impl<BT, P, W> IsTile<BT, P, W, LamAppNKG> for LamAppTile<BT>
where
    BT: IsBitTree,
    P: IsPath<W>,
    W: IsPathUnit,
{
    fn from(np: NodePath<P, W, LamAppNKG>) -> (PathToTile<BT, P, W>, Self)
    {
        match np.nodekind
        {
            LamAppNKG::Lam => {
                let (to_tile, in_tile) = split_raw_path::<BT,_,_,Shift1NodeKind>(&np.path);
                let res = LamAppTile {
                    tree_lam: BT::from(in_tile),
                    tree_app: BT::empty()
                };
                (to_tile, res)
            }
            LamAppNKG::App => todo!(),
        }
    }
}

