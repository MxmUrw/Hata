// use Term::
use crate::AlgebraLL::MutMonoid::Definition::*;
use crate::BitTree::Variant::BitTree32::Definition::*;
use crate::Node::NodeKind::Definition::*;
use crate::Node::NodeKindGroup::Example::LamAppNKG::*;
use crate::NodePath::Definition::*;
use crate::Path::Convert::*;
use crate::Path::Variant::SingleUnit::Definition::*;
use crate::Term::Convert::TreeToPath;
use crate::Term::Convert::TreeToTileSet;
use crate::Term::Convert::TileSetToTree;
use crate::Term::Path::Definition::*;
use crate::Term::Path::Instance::Display::*;
use crate::Term::Tree::Definition::*;
use crate::Term::Tree::Instance::Display::*;
use crate::Tile::Example::LamAppTile::*;
use crate::TileSet::Definition::*;

pub fn exectest() -> ()
{
    let a = t_plus();
    let res = TreeToPath::encode::<SingleUnitPath, u64>(&a);
    println!("The encoded tree is: {res}");

    // 1100101
    // let p_int = (1 << 6) | (1 << 5) | (1 << 2) | 1;
    // let p = SingleUnitPath
    //     {
    //         length: 8,
    //         value: p_int
    //     };

    // let res = split_raw_path::<BitTree32,_,_,Shift1NodeKind>(&p);
    // println!("The split path is: {} and {}", res.0.0, res.1.0);

    // let p1 = SingleUnitPath {
    //     length: 2,
    //     value: 0b10
    // };
    // let p2 = SingleUnitPath {
    //     length: 2,
    //     value: 0b00
    // };
    // println!("my paths are: {p1}, {p2}");

    // let mut ts : TileSet1<LamAppTile<BitTree32>, BitTree32,SingleUnitPath,u64,LamAppNKG> = TileSet1::empty();
    // println!("----------------------------------------------------");
    // println!("-- empty tile set");
    // println!("{ts}");

    // ts.append_single(NodePath::new(p1, LamAppNKG::App));
    // println!("----------------------------------------------------");
    // println!("-- with p1");
    // println!("{ts}");

    // ts.append_single(NodePath::new(p2, LamAppNKG::App));
    // println!("----------------------------------------------------");
    // println!("-- with p2");
    // println!("{ts}");

    println!("Encoding the term {a} to a tileset.");
    let res2 = TreeToTileSet::encode::<SingleUnitPath, u64>(&a);
    println!("The tileset is:\n{res2}");

    let res3 = TileSetToTree::decode(&res2);
    println!("The decoded term is: {res3}");
}
