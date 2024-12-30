use std::io;

use rustc_hash::FxHashMap;

fn remove_prefix<'a>(s: &'a str, prefix: &str) -> Option<&'a str> {
    (s.len() >= prefix.len() && s.bytes().zip(prefix.bytes()).all(|(a, b)| a == b))
        .then(|| &s[prefix.len()..])
}

fn count_possibilities<'a>(
    possibilities: &mut FxHashMap<&'a str, u64>,
    patterns: &[&str],
    design: &'a str,
) -> u64 {
    if design.is_empty() {
        1
    }
    else {
        possibilities.get(design).copied().unwrap_or_else(|| {
            let count = patterns
                .iter()
                .filter_map(|pattern| remove_prefix(design, pattern))
                .map(|design| count_possibilities(possibilities, patterns, design))
                .sum();
            possibilities.insert(design, count);
            count
        })
    }
}

fn main() -> io::Result<()> {
    let input = std::fs::read_to_string("input")?;
    let (patterns, designs) = input.split_once("\n\n").unwrap();
    let patterns: Vec<_> = patterns.trim().split(", ").collect();
    let designs: Vec<_> = designs.trim().lines().collect();
    let mut part_1 = 0;
    let mut part_2 = 0;
    let mut possibilities = FxHashMap::default();
    for design in &designs {
        let possibility_count = count_possibilities(&mut possibilities, &patterns, design);
        part_1 += (possibility_count != 0) as u64;
        part_2 += possibility_count;
    }
    println!("{part_1}");
    println!("{part_2}");
    Ok(())
}
