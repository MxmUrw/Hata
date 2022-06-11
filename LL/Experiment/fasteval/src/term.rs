
mod user;
use user::definition::*;

mod enc;
// use enc::path_::*;
use enc::bittree::*;

pub fn mtest() -> () {
    println!("hello!");
    // let t = t_plus();
    // println!("Term: {}", t);
    // println!("Encoded: {}", encode(&t));

    let tree = BitTree32{bits: (1 << 1) + (1 << 2) + (1 << 4) + (1 << 3) + (1 << 7)};
    println!("{tree}");
}



