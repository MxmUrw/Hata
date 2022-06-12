
use crate::Path::Definition::*;

#[derive(Debug, Clone, Copy)]
pub struct SingleUnitPath
{
    pub length: usize,
    pub value: u64,
}

impl SingleUnitPath
{
    fn push(&mut self, postpath:u64, length_postpath:usize)
    {
        self.value |= postpath << self.length;
        self.length += length_postpath;
    }
}


impl IsPath<u64> for SingleUnitPath
{
    fn push(&mut self, postpath: u64, length_postpath: usize)
    {
        SingleUnitPath::push(self, postpath, length_postpath);
    }
}



