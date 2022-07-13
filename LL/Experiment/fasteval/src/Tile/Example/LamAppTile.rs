use crate::BitTree::Definition::*;
use crate::Node::NodeKind::Definition::*;
use crate::Node::NodeKindGroup::Example::LamAppNKG::*;
use crate::NodePath::Definition::*;
use crate::NodePath::Instance::Display::*;
use crate::Path::Convert::*;
use crate::Path::Definition::*;
use crate::Path::Wrapper::PathToTile::*;
use crate::Tile::Definition::*;

use std::marker::PhantomData;
use std::ops::BitOr;

#[derive(Clone)]
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

impl<BT> BitOr for LamAppTile<BT>
where
    BT: IsBitTree + std::fmt::Display,
{
    type Output = LamAppTile<BT>;
    fn bitor(self, other: LamAppTile<BT>) -> LamAppTile<BT>
    {
        // println!("#########");
        // println!("# Computing bitor of: \n{}\n#### and\n{}", self.tree_app, other.tree_app);

        let tree_app = self.tree_app | other.tree_app;
        // println!("### result: \n{}", tree_app);
        let tree_lam = self.tree_lam | other.tree_lam;
        LamAppTile { tree_app, tree_lam }
    }
}

impl<BT, P, W> IsTile<BT, P, W, LamAppNKG> for LamAppTile<BT>
where
    BT: IsBitTree + std::fmt::Display,
    P: IsPath<W>,
    W: IsPathUnit,
{
    fn from(np: NodePath<P, W, LamAppNKG>) -> (PathToTile<BT, P, W>, Self)
    {
        // println!("Got the following nodepath: {np}, nodekind is: {}", &np.nodekind);
        match np.nodekind
        {
            LamAppNKG::Lam =>
            {
                // println!("Calling split lam, with {}", Shift1NodeKind::slice_shift());
                let (to_tile, in_tile) = split_raw_path::<BT, _, _, Shift1NodeKind>(&np.path);
                // println!("Got to_tile, in_tile");
                let res = LamAppTile {
                    tree_lam: BT::from(in_tile),
                    tree_app: BT::empty(),
                };
                (to_tile, res)
            }
            LamAppNKG::App =>
            {
                // println!("Calling split app, with {}", Shift0NodeKind::slice_shift());
                let (to_tile, in_tile) = split_raw_path::<BT, _, _, Shift0NodeKind>(&np.path);
                // println!("Got to_tile, in_tile");
                let res = LamAppTile {
                    tree_lam: BT::empty(),
                    tree_app: BT::from(in_tile),
                };
                (to_tile, res)
            }
        }
    }

    fn get(&self, path_in_tile: &P) -> Option<LamAppNKG>
    {
        if self.tree_lam.get_bit(path_in_tile)
        {
            Some(LamAppNKG::Lam)
        }
        else if self.tree_app.get_bit(path_in_tile)
        {
            Some(LamAppNKG::App)
        }
        else
        {
            None
        }
    }
}

impl<BT> std::fmt::Display for LamAppTile<BT>
where
    BT: IsBitTree + std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error>
    {
        write!(f, "app:\n{}\nlam:\n{}\n", self.tree_app, self.tree_lam)
    }
}
