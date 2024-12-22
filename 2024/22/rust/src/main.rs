#![feature(integer_sign_cast)]
#![feature(iterator_try_collect)]

use std::error::Error;

use rayon::iter::IntoParallelRefIterator as _;
use rayon::iter::ParallelIterator as _;
use rustc_hash::FxHashMap;

const PRUNE_MODULUS: u64 = 16777216;

fn next_secret_number(mut n: u64) -> u64 {
    n = (n ^ (n * 64)) % PRUNE_MODULUS;
    n = (n ^ (n / 32)) % PRUNE_MODULUS;
    n = (n ^ (n * 2048)) % PRUNE_MODULUS;
    n
}

fn part_1(secret_numbers: &[u64]) -> u64 {
    secret_numbers
        .iter()
        .copied()
        .map(|mut secret_number| {
            for _ in 0..2000 {
                secret_number = next_secret_number(secret_number);
            }
            secret_number
        })
        .sum()
}

fn part_2(secret_numbers: &[u64]) -> u64 {
    let total_bananas = secret_numbers
        .par_iter()
        .copied()
        .map(|mut secret| {
            let mut changes = 0;
            let mut bananas_by_sequence = FxHashMap::default();
            for i in 0..2000 {
                let new_secret = next_secret_number(secret);
                let change = (new_secret % 10).cast_signed() - (secret % 10).cast_signed();
                changes *= 20;
                changes += change + 10;
                changes %= const { 20_i64.pow(4) };
                secret = new_secret;
                if i >= 3 {
                    bananas_by_sequence.entry(changes).or_insert(secret % 10);
                }
            }
            bananas_by_sequence
        })
        .reduce_with(|mut total_bananas, bananas_by_sequence| {
            for (&sequence, &bananas) in &bananas_by_sequence {
                *total_bananas.entry(sequence).or_default() += bananas;
            }
            total_bananas
        })
        .unwrap();
    *total_bananas.values().max().unwrap()
}

fn main() -> Result<(), Box<dyn Error>> {
    let input: Vec<u64> = std::fs::read_to_string("input")?
        .lines()
        .map(str::parse)
        .try_collect()?;
    println!("{}", part_1(&input));
    println!("{}", part_2(&input));
    Ok(())
}
