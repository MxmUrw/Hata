

pub trait IsBitTree :
  Eq + std::hash::Hash
{
    fn full_height() -> usize;
    fn slice_height() -> usize;
}





