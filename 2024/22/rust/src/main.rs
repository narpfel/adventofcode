#![feature(iterator_try_collect)]

use std::error::Error;

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
    secret_numbers
        .iter()
        .copied()
        .enumerate()
        .fold(
            vec![(0, usize::MAX); 19_usize.pow(4)],
            |mut bananas_by_sequence, (monkey, mut secret)| {
                let mut changes = 0;
                for i in 0..2000 {
                    let new_secret = next_secret_number(secret);
                    let change = (new_secret % 10).cast_signed() - (secret % 10).cast_signed();
                    changes *= 19;
                    changes += change + 9;
                    changes %= const { 19_i64.pow(4) };
                    secret = new_secret;
                    if i >= 3 {
                        let (bananas, index) = &mut bananas_by_sequence[changes as usize];
                        if *index != monkey {
                            *index = monkey;
                            *bananas += secret % 10;
                        }
                    }
                }
                bananas_by_sequence
            },
        )
        .into_iter()
        .map(|(bananas, _)| bananas)
        .max()
        .unwrap()
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
