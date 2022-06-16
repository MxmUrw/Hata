

use std::string::*;
use std::fmt;

pub enum TreeTerm {
    Λ(String,Box<TreeTerm>),
    App(Box<TreeTerm>,Box<TreeTerm>),
    Var(String),
    Invalid()
}

macro_rules! Λ {
    ($a:ident,$t:expr) => {
        TreeTerm::Λ(stringify!($a).to_string(),Box::new($t))
    }
}

macro_rules! App {
    ($t:expr,$s:expr) => {
        TreeTerm::App(Box::new($t),Box::new($s))
    }
}

macro_rules! Var {
    ($a:ident) => {
        TreeTerm::Var(stringify!($a).to_string())
    }
}


pub fn t_plus() -> TreeTerm {
    Λ!(f, Λ!(g, Λ!(ξ, App!(Var!(g), App!(Var!(f), Var!(ξ))))))
}





