
use crate::Path::Definition::*;
use crate::Path::Wrapper::PathToTile::*;
use crate::NodePath::Definition::*;
use crate::BitTree::Definition::*;

use std::marker::PhantomData;


pub trait IsTile<BT,P,W,NKG> where
    BT : IsBitTree,
    P  : IsPath<W>,
    W  : IsPathUnit
{
    fn from(np: NodePath<P,W,NKG>) -> (PathToTile<BT,P,W>, Self);
}





