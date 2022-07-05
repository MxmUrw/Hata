

pub trait IsMutMonoid<A> where
{
    fn empty() -> Self;
    fn single(a:A) -> Self;
    fn append(&mut self, other: Self);
    fn append_single(&mut self, other: A);

    // writing `a * b` for append(a,b) we want the following to hold:
    //
    // 1. Monoid rules.
    // 2. a * [x] == append_single(a,x)
}


