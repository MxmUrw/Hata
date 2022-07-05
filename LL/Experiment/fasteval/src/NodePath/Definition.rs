
use std::marker::PhantomData;

pub struct NodePath<P,W,NKG> where
{
    nodekind : NKG,
    path: P,

    // phantoms
    phantom: PhantomData<W>
}





