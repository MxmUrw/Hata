
#![allow(mixed_script_confusables)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

mod term;
mod exec;
pub mod AlgebraLL;
pub mod Term;
pub mod Path;
pub mod BitTree;
pub mod Tile;
pub mod TileSet;
pub mod Node;
pub mod NodePath;


use term::*;
use exec::*;


fn main() {
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
//  -[ ] implement: fn: takes a path and creates a tile with only this bit set
//  -[ ] implement: type: tiledata: contains the relative variable paths
//  -[ ] implement: fn: creates tiledata from given tile-term
//  -[v] implement: type: tileset: contains multiple tiles
//  -[v] implement: fn: tileset-printing
//  -[v] implement: fn: takes a tree-term and creates a tile-term (tileset)
//  -[ ] implement: fn: shift tile {up,down}-{left,right} (this creates multiple tiles if we have over/under-flow)
//
//  -[ ] implement: fn: loop 1 of normalization algorithm
//  -[ ] implement: fn: loop 2 of normalization algorithm
//



