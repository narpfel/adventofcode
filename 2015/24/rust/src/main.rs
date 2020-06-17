use std::fs::read_to_string;

use itertools::Itertools;

type Value = u8;

fn subsequences<T: Clone, I: Into<Vec<T>>>(xs: I) -> impl Iterator<Item = Vec<T>> {
    let xs = xs.into();
    (0..xs.len() + 1).flat_map(move |l| xs.clone().into_iter().combinations(l))
}

fn weight(xs: &[Value]) -> u64 {
    xs.iter().map(|&v| v as u64).sum()
}

fn quantum_entanglement(xs: &[Value]) -> u64 {
    xs.iter().map(|&v| v as u64).product()
}

fn solve(target_weight: u64, weights: &[Value]) -> u64 {
    subsequences(weights)
        .filter(|xs| target_weight == weight(&xs))
        .map(|xs| quantum_entanglement(&xs))
        .min()
        .unwrap()
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input: Vec<Value> = read_to_string("input")?
        .lines()
        .map(str::parse)
        .collect::<Result<_, _>>()?;

    let part1 = weight(&input) / 3;
    let part2 = weight(&input) / 4;
    println!("{}", solve(part1, &input));
    println!("{}", solve(part2, &input));
    Ok(())
}
