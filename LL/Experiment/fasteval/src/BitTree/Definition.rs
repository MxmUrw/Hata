use crate::Node::NodeKind::Definition::*;
use crate::Path::Definition::*;
use crate::Path::Wrapper::PathInTile::*;
use std::ops::BitOr;

pub trait IsBitTree: Eq + std::hash::Hash + Sized + BitOr<Output = Self>
{
    fn full_height() -> usize;
    fn slice_height() -> usize;
    fn from<NK: IsNodeKind, P: IsPath<W>, W: IsPathUnit>(path: PathInTile<Self, P, W, NK>) -> Self;
    fn get_bit<P: IsPath<W>, W: IsPathUnit>(&self, p: &P) -> bool;
    fn empty() -> Self;
}
