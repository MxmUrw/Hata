use std::marker::PhantomData;

pub struct NodePath<P, W, NKG>
{
    pub path: P,
    pub nodekind: NKG,

    // phantoms
    phantom: PhantomData<W>,
}

impl<P, W, NKG> NodePath<P, W, NKG>
{
    pub fn new(path: P, nodekind: NKG) -> NodePath<P, W, NKG>
    {
        NodePath {
            path,
            nodekind,
            phantom: PhantomData,
        }
    }
}
