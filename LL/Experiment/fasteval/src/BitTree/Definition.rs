
use crate::Node::NodeKind::Definition::*;
use crate::Path::Definition::*;
use crate::Path::Wrapper::PathInTile::*;

pub trait IsBitTree : Eq + std::hash::Hash + Sized where
{
    fn full_height() -> usize;
    fn slice_height() -> usize;
    fn from<NK: IsNodeKind, P : IsPath<W>, W : IsPathUnit>(path: PathInTile<Self,P,W,NK>) -> Self;
    fn empty() -> Self;
}


