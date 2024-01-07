use std::{
    env::args,
    error::Error,
    fs::File,
};

fn main() -> Result<(), Box<dyn Error>> {
    let filename = args().nth(1).expect("Usage: md5 <filename>");
    let file = File::open(&filename)?;
    let bytes = unsafe { memmap2::MmapOptions::new().populate().map(&file) }?;
    println!(
        "{}  {}",
        std::str::from_utf8(&md5::format_digest(md5::md5(&bytes)))?,
        filename,
    );

    Ok(())
}
