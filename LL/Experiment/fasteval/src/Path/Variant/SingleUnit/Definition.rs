use crate::Path::Definition::*;
use more_asserts::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SingleUnitPath
{
    pub length: usize,
    pub value: u64,
}

impl SingleUnitPath
{
    fn push_at_leaf(&mut self, postpath: u64, length_postpath: usize)
    {
        self.value |= postpath << self.length;
        self.length += length_postpath;
    }
}

impl IsPathUnit for u64
{
    fn left() -> u64
    {
        0b0
    }
    fn right() -> u64
    {
        0b1
    }
}

impl IsPath<u64> for SingleUnitPath
{
    fn root() -> SingleUnitPath
    {
        SingleUnitPath {
            length: 0,
            value: 0,
        }
    }
    fn push_at_leaf(&mut self, postpath: u64, length_postpath: usize)
    {
        SingleUnitPath::push_at_leaf(self, postpath, length_postpath);
    }
    fn pop_at_root(&mut self, length_pop: usize) -> SingleUnitPath
    {
        // make sure that we have enough bits to pop
        debug_assert_le!(length_pop, self.length);

        // fill usize length lower bits with 1
        let mask = (1 << length_pop) - 1;

        // the popped value is
        let res = self.value & mask;

        // shift myself by length to the right
        self.value >>= length_pop;
        self.length -= length_pop;

        SingleUnitPath {
            value: res,
            length: length_pop,
        }
    }
    fn pop_at_root_bit(&mut self) -> bool
    {
        let bit_at_root = self.pop_at_root(1);
        bit_at_root.value != 0
    }
    fn length(&self) -> usize
    {
        self.length
    }
    fn as_path_unit(self) -> u64
    {
        self.value
    }
}
