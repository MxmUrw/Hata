
use crate::Term::Tree::Definition::*;
use std::fmt;

impl fmt::Display for TreeTerm
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result
    {
        match self
        {
            TreeTerm::Λ(var, t) =>
            {
                write!(f, "Λ {}. {}", var, t)
            },
            TreeTerm::App(t,s) => write!(f, "({} {})", t, s),
            TreeTerm::Var(v) => write!(f,"{}",v),
            TreeTerm::Invalid() => write!(f,"⊘")
        }
    }
}
