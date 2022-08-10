#![allow(mixed_script_confusables)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

pub mod AlgebraLL;
pub mod BitTree;
pub mod Node;
pub mod NodePath;
pub mod Path;
pub mod Term;
pub mod Tile;
pub mod TileSet;
pub mod Structure;
mod exec;
mod term;

use exec::*;
use term::*;

fn main()
{
    mtest();
    exectest();
}

////////////////////////////////////////
// Hello!
//
// Next steps:
//  -[v] make folders for our different path types in path::*
//  -[v] have three folders in term::*, namely for user terms, pure path terms, tiled terms
//  -[v] abstract path-term encoding (type and function) over an abstract path type (we currently only use the `push` functionality?)
//  -[v] implement: fn: takes a path and creates a tile with only this bit set
//  -[v] implement: type: tileset: contains multiple tiles
//  -[v] implement: fn: tileset-printing
//  -[v] implement: fn: takes a tree-term and creates a tile-term (tileset)
//  -[v] implement: fn: takes a tile-term and recreates a tree-term
//  -[ ] implement: type: write IndexingTrie which gives us the search structure for an array of tiles
//  -[v] (diff arch) implement: type: tiledata: contains the relative variable paths
//  -[v] implement: fn: creates tiledata from given tile-term
//  -[ ] implement: fn: shift tile {up,down}-{left,right} (this creates multiple tiles if we have over/under-flow)
//
//  -[ ] implement: fn: loop 1 of normalization algorithm
//  -[ ] implement: fn: loop 2 of normalization algorithm
//
