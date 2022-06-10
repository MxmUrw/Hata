
use std::string::*;
use std::fmt;
use std::vec::*;
use std::collections::HashMap;
use std::hash::Hash;

use super::super::user::*;


////////////////////////////////////////////////////////////////
// Paths

#[derive(Debug, Clone, Copy)]
pub struct Path(u64);

impl Path {
    fn push(self, length_prepath:usize, prepath:u64) -> Self {
        match self {
            Path(val) => Path((val << length_prepath) | prepath)
        }
    }
}

impl fmt::Display for Path {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Path(val) => write!(f, "{:b}", val)
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct FullPath(u64,u64);

impl FullPath {
    fn push(self, length_postpath:u64, postpath:u64) -> Self {
        match self {
            FullPath(len,val) => FullPath(len + length_postpath, val | (postpath << len))
        }
    }

    fn with_fixed_length(&self) -> Path {
        match self {
            FullPath(len,p) => Path(p | (1 << len))
        }
    }
}

impl fmt::Display for FullPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FullPath(len,val) => write!(f, "{:b}", val)
        }
    }
}




