use std::iter::from_fn;

const MODULUS: u64 = 2147483647;

fn lehmer_rng(m: u64, a: u64, x: u64) -> u64 {
    (a * x) % m
}

fn generator(a: u64, mut x: u64) -> impl Iterator<Item = u64> {
    from_fn(move || {
        x = lehmer_rng(MODULUS, a, x);
        Some(x)
    })
}

fn solve(
    length: usize,
    a: u64,
    pa: impl Fn(&u64) -> bool,
    b: u64,
    pb: impl Fn(&u64) -> bool,
) -> usize {
    generator(16807, a)
        .filter(pa)
        .zip(generator(48271, b).filter(pb))
        .take(length)
        .filter(|(x, y)| (x & 0xffff) == (y & 0xffff))
        .count()
}

fn part1(a: u64, b: u64) -> usize {
    solve(40_000_000, a, |_| true, b, |_| true)
}

fn is_multiple_of(a: u64, b: u64) -> bool {
    (b % a) == 0
}

fn part2(a: u64, b: u64) -> usize {
    solve(
        5_000_000,
        a,
        |&x| is_multiple_of(4, x),
        b,
        |&x| is_multiple_of(8, x),
    )
}

fn main() {
    println!("{}", part1(116, 299));
    println!("{}", part2(116, 299));
}
