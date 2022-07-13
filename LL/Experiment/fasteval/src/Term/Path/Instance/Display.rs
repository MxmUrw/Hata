use crate::Path::Definition::*;
use crate::Term::Path::Definition::*;

use std::fmt;

impl<P, W> fmt::Display for PathTerm<P, W>
where
    P: IsPath<W>,
    W: IsPathUnit,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result
    {
        fn write_vec<T: fmt::Display>(f: &mut fmt::Formatter<'_>, xs: &Vec<T>) -> fmt::Result
        {
            write!(f, "[")?;
            for x in xs
            {
                write!(f, "{}, ", x);
            }
            write!(f, "]")?;
            Ok(())
        }
        fn write_tuple_vec<T: fmt::Display>(
            f: &mut fmt::Formatter<'_>,
            xs: &Vec<(T, Vec<T>)>,
        ) -> fmt::Result
        {
            write!(f, "[")?;
            for (a, xs) in xs
            {
                write!(f, "{} ", a)?;
                write_vec(f, xs)?;
                write!(f, ", ")?;
            }
            write!(f, "]")?;
            Ok(())
        }

        write!(f, "\napp: ")?;
        write_vec(f, &self.app)?;
        write!(f, "\nΛ  : ")?;
        write_tuple_vec(f, &self.λ)?;
        write!(f, "\n")?;
        Ok(())
    }
}
