use std::fmt;
use std::fmt::Write;

use md5::md5;

const INPUT: &str = "iwrupvqb";

fn find_hash_lower_than(maximum_value: u128) -> Result<u64, fmt::Error> {
    let mut buf = INPUT.to_string();
    for n in 0.. {
        buf.truncate(INPUT.len());
        write!(buf, "{n}")?;
        let hash = md5(buf.as_bytes());
        let hash = u128::from_be_bytes(hash);
        if hash < maximum_value {
            return Ok(n);
        }
    }
    unreachable!()
}

fn main() -> Result<(), fmt::Error> {
    println!(
        "{}",
        find_hash_lower_than(0x0000_1000_0000_0000_0000_0000_0000_0000)?,
    );
    println!(
        "{}",
        find_hash_lower_than(0x0000_0100_0000_0000_0000_0000_0000_0000)?,
    );
    Ok(())
}
