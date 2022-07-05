

// use Term::
use crate::Term::Path::Definition::*;
use crate::Term::Path::Instance::Display::*;
use crate::Term::Tree::Definition::*;
use crate::BitTree::Variant::BitTree32::Definition::*;
use crate::Path::Variant::SingleUnit::Definition::*;
use crate::Path::Convert::*;
use crate::Term::Convert::TreeToPath;
use crate::NodeKind::Definition::*;

pub fn exectest() -> ()
{
    let a = t_plus();
    let res = TreeToPath::encode::<SingleUnitPath,u64>(&a);
    println!("The encoded tree is: {res}");

    // 1100101
    let p_int = (1 << 6) | (1 << 5) | (1 << 2) | 1;
    let p = SingleUnitPath
        {
            length: 8,
            value: p_int
        };

    let res = split_raw_path::<BitTree32,_,_,Shift1NodeKind>(&p);
    println!("The split path is: {} and {}", res.0.0, res.1.0);

}



