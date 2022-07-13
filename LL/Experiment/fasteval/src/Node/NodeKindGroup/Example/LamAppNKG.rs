// use crate::Node::NodeKindGroup::Definition::*;

use std::fmt;

pub enum LamAppNKG
{
    Lam,
    App,
}

impl fmt::Display for LamAppNKG
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result
    {
        match self
        {
            LamAppNKG::Lam => write!(f, "lam"),
            LamAppNKG::App => write!(f, "app"),
        }
    }
}

// impl NodeKindGroup for LamAppNKG
// {}
