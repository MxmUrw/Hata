
use std::string::*;
use std::fmt;

pub enum ΛTermUser {
    Λ(String,Box<ΛTermUser>),
    App(Box<ΛTermUser>,Box<ΛTermUser>),
    Var(String)
}

macro_rules! Λ {
    ($a:ident,$t:expr) => {
        ΛTermUser::Λ(stringify!($a).to_string(),Box::new($t))
    }
}

macro_rules! App {
    ($t:expr,$s:expr) => {
        ΛTermUser::App(Box::new($t),Box::new($s))
    }
}

macro_rules! Var {
    ($a:ident) => {
        ΛTermUser::Var(stringify!($a).to_string())
    }
}

fn tPlus() -> ΛTermUser {
    Λ!(f, Λ!(g, Λ!(ξ, App!(Var!(g), App!(Var!(f), Var!(ξ))))))
}

impl fmt::Display for ΛTermUser {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ΛTermUser::Λ(var, t) => {
                write!(f, "Λ {}. {}", var, t)
            },
            ΛTermUser::App(t,s) => write!(f, "({} {})", t, s),
            ΛTermUser::Var(v) => write!(f,"{}",v)
        }
    }
}




pub fn mtest() -> () {
    println!("hello!");
    println!("Term: {}", tPlus())
}



