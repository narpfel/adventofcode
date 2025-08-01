const MODULUS: u64 = 2147483647;

fn lehmer_rng(m: u64, a: u64, x: u64) -> u64 {
    (a * x) % m
}

fn solve(
    length: usize,
    mut a: u64,
    pa: impl Fn(&u64) -> bool,
    mut b: u64,
    pb: impl Fn(&u64) -> bool,
) -> usize {
    let mut result = 0;

    for _ in 0..length {
        loop {
            a = lehmer_rng(MODULUS, 16807, a);
            if pa(&a) {
                break;
            }
        }
        loop {
            b = lehmer_rng(MODULUS, 48271, b);
            if pb(&b) {
                break;
            }
        }
        if (a & 0xffff) == (b & 0xffff) {
            result += 1;
        }
    }
    result
}

fn part1(a: u64, b: u64) -> usize {
    solve(40_000_000, a, |_| true, b, |_| true)
}

fn part2(a: u64, b: u64) -> usize {
    solve(
        5_000_000,
        a,
        |x| x.is_multiple_of(4),
        b,
        |x| x.is_multiple_of(8),
    )
}

fn main() {
    println!("{}", part1(116, 299));
    println!("{}", part2(116, 299));
}
