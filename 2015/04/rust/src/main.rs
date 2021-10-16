use std::fmt;
use std::fmt::Write;

use md5::format_digest;
use md5::md5;

const INPUT: &str = "iwrupvqb";

fn lowest_with_n_zeroes(leading_zeroes_count: u64) -> Result<u64, fmt::Error> {
    let leading_zeroes = "0".repeat(leading_zeroes_count as _);
    let mut buf = INPUT.to_string();
    for n in 0.. {
        buf.truncate(INPUT.as_bytes().len());
        write!(buf, "{}", n)?;
        let digest = format_digest(md5(buf.as_bytes()));
        if digest.starts_with(leading_zeroes.as_bytes()) {
            return Ok(n);
        }
    }
    unreachable!()
}

fn main() -> Result<(), fmt::Error> {
    println!("{}", lowest_with_n_zeroes(5)?);
    println!("{}", lowest_with_n_zeroes(6)?);
    Ok(())
}
