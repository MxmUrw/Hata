use std::marker::PhantomData;

use crate::Path::Definition::*;

pub struct PathTerm<P, W>
where
    P: IsPath<W>,
    W: IsPathUnit,
{
    // data
    pub app: Vec<P>,
    pub λ: Vec<(P, Vec<P>)>,

    // phantoms
    phantom: PhantomData<W>,
}

impl<P, W> PathTerm<P, W>
where
    P: IsPath<W>,
    W: IsPathUnit,
{
    pub fn empty() -> Self
    {
        PathTerm {
            app: vec![],
            λ: vec![],
            phantom: PhantomData,
        }
    }

    pub fn append(&mut self, other: &mut PathTerm<P, W>)
    {
        self.app.append(&mut other.app);
        self.λ.append(&mut other.λ);
    }
}
