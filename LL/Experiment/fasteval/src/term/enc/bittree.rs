
use std::string::*;
use std::fmt;
use std::vec::*;
use std::collections::HashMap;
use std::hash::Hash;

/// A single bit-tree.
///
/// Layout:
/// 1
/// 2 3
/// 4 5 6 7
/// 8 ... 15
/// 16 ... 31
///
pub struct BitTree32
{
    pub bits: u32
}

impl BitTree32
{

}


////////////////////////////////////////////////////
// Printing trees
impl fmt::Display for BitTree32
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result
    {
        // The bits we will print,
        // this is a copy of self.
        let mut bits = self.bits;

        // first we say how to print a single line
        fn print_single_line(f: &mut fmt::Formatter, bits: &mut u32, line_number: u32, number_of_bits_to_print: usize, line_width: usize) -> fmt::Result
        {
            let l = line_number;
            let n = number_of_bits_to_print;
            let w = line_width;

            // print line number
            write!(f, "{}|", l);

            // Start by printing empty space for the left side of the pyramid.
            // We need ((w - n) / 2) skips on the left, but each skip consists
            // of two spaces.
            write!(f, "{}", " ".repeat(w - n))?;

            // Now do the following n times: take lsb, print it with spaces, shift bits
            for _ in 0..n
            {
                // get and print
                let bit = *bits & 0b1;
                write!(f,"{} ", bit)?;

                // shift
                *bits >>= 1;
            }
            Ok(())
        }


        // we have a first underflow bit
        let underflow = bits & 0b1;
        bits >>= 1;
        writeln!(f,"underflow: {underflow}");

        // we have 5 lines each double the size of the previous
        // - `i` is the line number
        // - `n` is the number of entries of the current line
        let mut n = 1;
        for i in 0..5
        {
            print_single_line(f, &mut bits, i, n, 16)?;
            writeln!(f,"")?;
            n *= 2;
        }

        Ok(())
    }
}



