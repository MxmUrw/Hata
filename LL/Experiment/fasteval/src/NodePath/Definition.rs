
use std::marker::PhantomData;

pub struct NodePath<P,W,NKG> where
{
    pub path: P,
    pub nodekind : NKG,

    // phantoms
    phantom: PhantomData<W>
}





