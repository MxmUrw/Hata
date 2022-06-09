
mod user;
use user::*;

mod enc;
use enc::*;

pub fn mtest() -> () {
    println!("hello!");
    let t = t_plus();
    println!("Term: {}", t);
    println!("Encoded: {}", encode(&t));
}



