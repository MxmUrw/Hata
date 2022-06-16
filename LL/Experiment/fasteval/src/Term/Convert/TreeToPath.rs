
use std::hash::*;
use std::collections::HashMap;

use crate::Path::Definition::*;
use crate::Term::Tree::Definition::*;
use crate::Term::Path::Definition::*;


pub fn run<P,W>(ts: &TreeTerm) -> PathTerm<P,W> where
    P : IsPath<W>,
    W : IsPathUnit
{
    todo!()
}

pub fn encode<Path,W>(ts: &TreeTerm) -> PathTerm<Path,W> where
    Path : IsPath<W>,
    W : IsPathUnit
{
    encode_(ts,&Path::root()).0
}


fn encode_<Path,W>(ts: &TreeTerm, curpath_immut: &Path) -> (PathTerm<Path,W>, HashMap<String,Vec<Path>>) where
    Path : IsPath<W>,
    W : IsPathUnit
{
    let mut curpath = curpath_immut.clone();
    println!("Encoding, curpath={}", curpath);
    match ts {
        TreeTerm::Λ(var,term) =>
        {
            curpath.push(W::left(), 1);
            let (mut t_, mut vars) = encode_(term, &curpath);
            let var_paths = match vars.remove(var) {
                None => vec![],
                Some(a) => a
            };
            t_.λ.push((curpath,var_paths));
            (t_, vars)
        },
        TreeTerm::App(t,s) =>
        {
            // create the left and right paths
            let mut path_l = curpath.clone();
            let mut path_r = curpath.clone();
            path_l.push(W::left(), 1);
            path_r.push(W::right(), 1);

            // call myself recursively
            let (mut t_, mut tvars) = encode_(t, &path_l);
            let (mut s_, mut svars) = encode_(s, &path_r);
            t_.append(&mut s_);
            t_.app.push(curpath);
            merge_vec_hashmaps(&mut tvars, &mut svars);
            (t_, tvars)
        },
        TreeTerm::Var(s) =>
        {
            let mut vars = HashMap::new();
            vars.insert(s.clone(), vec![curpath]);
            (PathTerm::empty(), vars)
        },
        TreeTerm::Invalid() => (PathTerm::empty(), HashMap::new())
    }
}


///////////////////////////////////////////////////////////
// helpers

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



