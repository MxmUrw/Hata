
use std::marker::PhantomData;

use crate::Path::Definition::*;

pub struct PathTerm<P,WordType> where
    P : IsPath<WordType>
{
    // data
    app : Vec<P>,
    λ   : Vec<(P,Vec<P>)>,

    // phantoms
    phantom : PhantomData<WordType>,
}

impl<P,WordType> PathTerm<P,WordType> where
    P : IsPath<WordType>
{
    pub fn empty() -> Self
    {
        PathTerm {app: vec![], λ: vec![], phantom: PhantomData}
    }

    pub fn append(&mut self, other: &mut PathTerm<P,WordType>)
    {
        self.app.append(&mut other.app);
        self.λ.append(&mut other.λ);
    }
}


