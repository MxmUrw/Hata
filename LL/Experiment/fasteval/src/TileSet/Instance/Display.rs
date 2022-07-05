
use crate::TileSet::Definition::*;
use crate::TileSet::Definition::*;
use crate::BitTree::Definition::*;
use crate::Tile::Definition::*;
use crate::Path::Definition::*;
use crate::Path::Wrapper::PathToTile::*;
use crate::NodePath::Definition::*;

use std::string::*;
use std::fmt;
use std::vec::*;
use std::collections::HashMap;
use std::hash::Hash;


impl<T,BT,P,W,NKG1> fmt::Display for TileSet1<T,BT,P,W,NKG1> where
    T: IsTile<BT,P,W,NKG1> + Clone + fmt::Display,
    BT: IsBitTree + Clone,
    P: IsPath<W>,
    W: IsPathUnit + Clone
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result
    {
        for (k,v) in &self.tiles1
        {
            let p = &k.0;
            let tile = v;
            write!(f, "---------------------------\npath: {p}\n{tile}")?
        }
        Ok(())
    }
}


