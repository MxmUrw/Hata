
use crate::TileSet::Definition::*;
use crate::BitTree::Definition::*;
use crate::Tile::Definition::*;
use crate::Path::Definition::*;
use crate::AlgebraLL::MutMonoid::Definition::*;
use crate::NodePath::Definition::*;


impl<BT,P,W,NKG> IsMutMonoid<NodePath<P,W,NKG>> for TileSet<BT,P,W> where
    BT: IsBitTree,
    P : IsPath<W>,
    W: IsPathUnit
{
    fn empty() -> TileSet<BT,P,W>
    {
        todo!()
    }

    fn single(a: NodePath<P,W,NKG>) -> TileSet<BT,P,W>
    {
        todo!()
    }

    fn append(&mut self, other: TileSet<BT,P,W>)
    {
        todo!()
    }

    fn append_single(&mut self, other: NodePath<P,W,NKG>)
    {
        todo!()
    }
}






