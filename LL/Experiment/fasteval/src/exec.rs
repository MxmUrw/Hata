

// use Term::
use crate::Term::Path::Definition::*;
use crate::Term::Path::Instance::Display::*;
use crate::Term::Tree::Definition::*;
use crate::Path::Variant::SingleUnit::Definition::*;
use crate::Term::Convert::TreeToPath;

pub fn exectest() -> ()
{
    let a = t_plus();
    let res = TreeToPath::encode::<SingleUnitPath,u64>(&a);
    println!("The encoded tree is: {res}");

}



