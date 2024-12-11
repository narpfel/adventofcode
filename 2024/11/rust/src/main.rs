use std::io;

use rustc_hash::FxHashMap;

fn blink(cache: &mut FxHashMap<(u64, usize), u64>, stone: u64, n: usize) -> u64 {
    match cache.get(&(stone, n)) {
        Some(&result) => result,
        None => {
            let result = {
                if n == 0 {
                    1
                }
                else if stone == 0 {
                    blink(cache, 1, n - 1)
                }
                else {
                    let digit_count = stone.ilog10() + 1;
                    if digit_count % 2 == 0 {
                        let half = 10_u64.pow(digit_count / 2);
                        blink(cache, stone / half, n - 1) + blink(cache, stone % half, n - 1)
                    }
                    else {
                        blink(cache, stone * 2024, n - 1)
                    }
                }
            };
            cache.insert((stone, n), result);
            result
        }
    }
}

fn solve(cache: &mut FxHashMap<(u64, usize), u64>, stones: &[u64], blinks: usize) -> u64 {
    stones
        .iter()
        .map(|&stone| blink(cache, stone, blinks))
        .sum()
}

fn main() -> io::Result<()> {
    let stones = std::fs::read_to_string("input")?
        .split_whitespace()
        .map(|s| s.parse().unwrap())
        .collect::<Vec<_>>();

    let mut cache = FxHashMap::default();
    cache.reserve(200_000);
    println!("{}", solve(&mut cache, &stones, 25));
    println!("{}", solve(&mut cache, &stones, 75));
    Ok(())
}
