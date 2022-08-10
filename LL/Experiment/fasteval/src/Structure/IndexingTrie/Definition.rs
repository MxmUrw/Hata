
// trait IsIndexingTriePath<const N : usize>
// {
    
// }


struct IndexingTrie<PathSegmentBits>
{
    node: Option<usize>,
    bits: PathSegmentBits,
    next: Vec<Self>
}


