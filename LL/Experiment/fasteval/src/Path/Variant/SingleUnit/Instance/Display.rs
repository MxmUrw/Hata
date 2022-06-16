
use crate::Path::Variant::SingleUnit::Definition::*;
use std::fmt;

///////////////////////////////////////////////////////////////////
// Printing
impl fmt::Display for SingleUnitPath
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result
    {
        write!(f, "*{:0width$b}", self.value, width = self.length)
    }
}



