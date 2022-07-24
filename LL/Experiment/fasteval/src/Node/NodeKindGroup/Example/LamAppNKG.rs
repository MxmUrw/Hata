// use crate::Node::NodeKindGroup::Definition::*;

use std::fmt;

pub enum LamAppNKG<P>
{
    Lam(Vec<P>),
    App,
}

impl<P> fmt::Display for LamAppNKG<P>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result
    {
        match self
        {
            LamAppNKG::Lam(_) => write!(f, "lam"),
            LamAppNKG::App => write!(f, "app"),
        }
    }
}

// impl NodeKindGroup for LamAppNKG
// {}
