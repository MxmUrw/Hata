





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


