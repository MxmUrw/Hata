use crate::NodePath::Definition::*;
use crate::Path::Definition::*;

use std::fmt;

impl<P, W, NKG1> fmt::Display for NodePath<P, W, NKG1>
where
    P: IsPath<W>,
    W: IsPathUnit,
    NKG1: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result
    {
        write!(f, "{}:{}", self.path, self.nodekind)
    }
}
