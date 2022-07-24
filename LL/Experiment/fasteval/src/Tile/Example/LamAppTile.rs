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
use std::collections::HashMap;

#[derive(Clone)]
pub struct LamAppTile<BT, P, W>
where
    BT: IsBitTree,
    P : IsPath<W>,
    W : IsPathUnit
{
    // path : P,
    tree_lam: BT,
    tree_app: BT,
    vars_lam: HashMap<P, Vec<P>>,
    phantom: PhantomData<W>,
}

// impl<BT,P,W> Tile<BT,P,W> where
// impl<BT> LamAppTile<BT, P, W>
// where
//     BT: IsBitTree,
//     // P : IsPath<W>,
//     // W : IsPathUnit
// {
//     // pub fn new_single_λ(_p: &P) -> Self
//     // {
//     //     todo!()
//     // }
// }


impl<BT, P, W> BitOr for LamAppTile<BT, P, W>
where
    BT: IsBitTree + std::fmt::Display,
    P : IsPath<W>,
    W : IsPathUnit
{
    type Output = LamAppTile<BT, P, W>;
    fn bitor(self, other: LamAppTile<BT, P, W>) -> LamAppTile<BT, P, W>
    {
        // println!("#########");
        // println!("# Computing bitor of: \n{}\n#### and\n{}", self.tree_app, other.tree_app);

        let tree_app = self.tree_app | other.tree_app;
        // println!("### result: \n{}", tree_app);
        let tree_lam = self.tree_lam | other.tree_lam;

        // merge the hashmaps
        let vars_lam = self.vars_lam.into_iter().chain(other.vars_lam).collect();

        LamAppTile { tree_app, tree_lam, vars_lam, phantom: PhantomData }
    }
}

impl<BT, P, W> IsTile<BT, P, W, LamAppNKG<P>> for LamAppTile<BT, P, W>
where
    BT: IsBitTree + std::fmt::Display,
    P: IsPath<W>,
    W: IsPathUnit,
{
    fn from(np: NodePath<P, W, LamAppNKG<P>>) -> (PathToTile<BT, P, W>, Self)
    {
        // println!("Got the following nodepath: {np}, nodekind is: {}", &np.nodekind);
        match np.nodekind
        {
            LamAppNKG::Lam(vars) =>
            {
                // println!("Calling split lam, with {}", Shift1NodeKind::slice_shift());
                let (to_tile, in_tile) = split_raw_path::<BT, _, _, Shift1NodeKind>(&np.path);

                // the hashmap containing vars
                // if some vars are given, we insert them
                let mut varmap = HashMap::new();
                varmap.insert(in_tile.0.clone(), vars);

                // println!("Got to_tile, in_tile");
                let res = LamAppTile {
                    tree_lam: BT::from(in_tile),
                    tree_app: BT::empty(),
                    vars_lam: varmap,
                    phantom: PhantomData,
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
                    vars_lam: HashMap::new(),
                    phantom: PhantomData,
                };
                (to_tile, res)
            }
        }
    }

    fn get(&self, path_in_tile: &P) -> Option<LamAppNKG<P>>
    {
        if self.tree_lam.get_bit(path_in_tile)
        {
            let vars = if let Some(vars) = self.vars_lam.get(path_in_tile)
            {vars.clone()} else {vec![]};

            Some(LamAppNKG::Lam(vars))
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

impl<BT, P, W> std::fmt::Display for LamAppTile<BT, P, W>
where
    BT: IsBitTree + std::fmt::Display,
    P: IsPath<W>,
    W: IsPathUnit,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error>
    {
        write!(f, "app:\n{}\nlam:\n{}\n", self.tree_app, self.tree_lam)
    }
}

