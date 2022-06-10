
use std::string::*;
use std::fmt;
use std::vec::*;
use std::collections::HashMap;
use std::hash::Hash;

use super::user::*;

////////////////////////////////////////////////////////////////
// Paths

#[derive(Debug, Clone, Copy)]
struct Path(u64);

impl Path {
    fn push(self, length_prepath:usize, prepath:u64) -> Self {
        match self {
            Path(val) => Path((val << length_prepath) | prepath)
        }
    }
}

impl fmt::Display for Path {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Path(val) => write!(f, "{:b}", val)
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct FullPath(u64,u64);

impl FullPath {
    fn push(self, length_postpath:u64, postpath:u64) -> Self {
        match self {
            FullPath(len,val) => FullPath(len + length_postpath, val | (postpath << len))
        }
    }

    fn with_fixed_length(&self) -> Path {
        match self {
            FullPath(len,p) => Path(p | (1 << len))
        }
    }
}

impl fmt::Display for FullPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FullPath(len,val) => write!(f, "{:b}", val)
        }
    }
}


////////////////////////////////////////////////////////////////
// Encoded terms

pub struct EncTerm {
    app : Vec<Path>,
    λ   : Vec<(Path,Vec<Path>)>,
}

impl EncTerm {
    fn empty() -> Self {
        EncTerm {app: vec![], λ: vec![]}
    }
    fn append(&mut self, other: &mut EncTerm) {
        self.app.append(&mut other.app);
        self.λ.append(&mut other.λ);
    }
}

fn merge_vec_hashmaps<K: Eq + Hash + Clone,V>(xs: &mut HashMap<K,Vec<V>>, ys: &mut HashMap<K,Vec<V>>) -> () {
    for (k,y) in ys {
        xs.entry(k.clone())
            .and_modify(|v| v.append(y))
            .or_insert(y.drain(0..).collect());
    }
    // ys.into_iter()
    //     .map(move |(k,y)| {
    //     });
}

////////////////////////////
// encoding them
pub fn encode(ts: &UserTerm) -> EncTerm {
    encode_(ts,FullPath(0,0)).0
}
fn encode_(ts: &UserTerm, curpath: FullPath) -> (EncTerm,HashMap<String,Vec<Path>>) {
    println!("Encoding, curpath={curpath}");
    match ts {
        UserTerm::Λ(var,term) => {
            let (mut t_, mut vars) = encode_(term, curpath.push(1,0b0));
            let var_paths = match vars.remove(var) {
                None => vec![],
                Some(a) => a
            };
            t_.λ.push((curpath.with_fixed_length(),var_paths));
            (t_, vars)
        },
        UserTerm::App(t,s) => {
            let (mut t_, mut tvars) = encode_(t, curpath.push(1,0b0));
            let (mut s_, mut svars) = encode_(s, curpath.push(1,0b1));
            t_.append(&mut s_);
            t_.app.push(curpath.with_fixed_length());
            merge_vec_hashmaps(&mut tvars, &mut svars);
            (t_, tvars)
        },
        UserTerm::Var(s) => {
            let mut vars = HashMap::new();
            vars.insert(s.clone(), vec![curpath.with_fixed_length()]);
            (EncTerm::empty(), vars)
        },
        UserTerm::Invalid() => (EncTerm::empty(), HashMap::new())
    }
}


////////////////////////////
// printing them
impl fmt::Display for EncTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn write_vec<T:fmt::Display>(f: &mut fmt::Formatter<'_>, xs: &Vec<T>) -> fmt::Result {
            write!(f,"[")?;
            for x in xs {
                write!(f,"{}, ", x);
            }
            write!(f,"]")?;
            Ok(())
        }
        fn write_tuple_vec<T:fmt::Display>(f: &mut fmt::Formatter<'_>, xs: &Vec<(T,Vec<T>)>) -> fmt::Result {
            write!(f,"[")?;
            for (a,xs) in xs {
                write!(f,"{} ", a)?;
                write_vec(f,xs)?;
                write!(f,", ")?;
            }
            write!(f,"]")?;
            Ok(())
        }

        match self {
            EncTerm {app,λ} => {
                write!(f,"\napp: ")?;
                write_vec(f, app)?;
                write!(f,"\nΛ  : ")?;
                write_tuple_vec(f, λ)?;
                write!(f,"\n")?;
            }
        };
        Ok(())
    }
}




