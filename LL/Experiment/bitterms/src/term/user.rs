
use std::string::*;
use std::fmt;

pub enum UserTerm {
    Λ(String,Box<UserTerm>),
    App(Box<UserTerm>,Box<UserTerm>),
    Var(String),
    Invalid()
}

macro_rules! Λ {
    ($a:ident,$t:expr) => {
        UserTerm::Λ(stringify!($a).to_string(),Box::new($t))
    }
}

macro_rules! App {
    ($t:expr,$s:expr) => {
        UserTerm::App(Box::new($t),Box::new($s))
    }
}

macro_rules! Var {
    ($a:ident) => {
        UserTerm::Var(stringify!($a).to_string())
    }
}

impl fmt::Display for UserTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UserTerm::Λ(var, t) => {
                write!(f, "Λ {}. {}", var, t)
            },
            UserTerm::App(t,s) => write!(f, "({} {})", t, s),
            UserTerm::Var(v) => write!(f,"{}",v),
            UserTerm::Invalid() => write!(f,"⊘")
        }
    }
}


pub fn t_plus() -> UserTerm {
    Λ!(f, Λ!(g, Λ!(ξ, App!(Var!(g), App!(Var!(f), Var!(ξ))))))
}


