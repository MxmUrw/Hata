



////////////////////////////////////////////////////////////////
// Encoded terms


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
