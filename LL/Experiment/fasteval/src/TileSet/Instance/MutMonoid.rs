
use crate::TileSet::Definition::*;
use crate::BitTree::Definition::*;
use crate::Tile::Definition::*;
use crate::Path::Definition::*;
use crate::Path::Wrapper::PathToTile::*;
use crate::AlgebraLL::MutMonoid::Definition::*;
use crate::NodePath::Definition::*;

use std::hash::*;
use std::marker::PhantomData;
use std::collections::HashMap;
use std::ops::BitOr;

// TODO: remove clone bound on BT?
impl<T,BT,P,W,NKG1> IsMutMonoid<NodePath<P,W,NKG1>> for TileSet1<T,BT,P,W,NKG1> where
    T: IsTile<BT,P,W,NKG1> + Clone,
    BT: IsBitTree + Clone,
    P: IsPath<W>,
    W: IsPathUnit + Clone
{
    fn empty() -> TileSet1<T,BT,P,W,NKG1>
    {
        TileSet1
        {
            tiles1: HashMap::new(),
            phantomNKG1: PhantomData
        }
    }

    fn single(np: NodePath<P,W,NKG1>) -> TileSet1<T,BT,P,W,NKG1>
    {
        let mut map = HashMap::new();
        let (path,tile) = T::from(np);
        map.insert(path,tile);
        TileSet1
        {
            tiles1: map,
            phantomNKG1: PhantomData
        }
    }

    fn append(&mut self, other: TileSet1<T,BT,P,W,NKG1>)
    {
        merge_hashmaps_with(&mut self.tiles1, other.tiles1, |t,s| (t | s))
    }

    fn append_single(&mut self, other: NodePath<P,W,NKG1>)
    {
        let (path,tile) = T::from(other);
        self.tiles1.entry(path)
            .and_modify(|v| *v = v.clone() | tile.clone())
            .or_insert(tile);
    }
}


fn merge_hashmaps_with<K: Eq + Hash + Clone,V : Clone,FType>
    (xs: &mut HashMap<K,V>,
     ys: HashMap<K,V>,
     f: FType
    )
     -> ()
    where
    FType: Fn(V,V) -> V
{
    for (k,y) in ys
    {
        xs.entry(k.clone())
            .and_modify(|v| *v = f(v.clone(),y.clone()))
            .or_insert(y.clone());
    }
    // ys.into_iter()
    //     .map(move |(k,y)| {
    //     });
}



