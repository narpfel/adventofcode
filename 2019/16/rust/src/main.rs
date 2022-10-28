use std::fs::read_to_string;

fn fft(xs: &[u8]) -> Vec<u8> {
    (0..xs.len())
        .map(|i| {
            pattern(i + 1)
                .zip(xs.iter())
                .map(|(p, &x)| i64::from(p) * i64::from(x))
                .sum()
        })
        .map(|x: i64| i64::abs(x % 10) as u8)
        .collect()
}

fn fft_part2(xs: &[u8]) -> Vec<u8> {
    let mut sums: Vec<_> = xs
        .iter()
        .rev()
        .scan(0, |acc, &x| {
            *acc += i64::from(x);
            Some(i64::abs(*acc % 10) as u8)
        })
        .collect();
    sums.reverse();
    sums
}

fn pattern(i: usize) -> impl Iterator<Item = i8> {
    [0, 1, 0, -1]
        .iter()
        .flat_map(move |x| std::iter::repeat(x).take(i))
        .cycle()
        .skip(1)
        .cloned()
}

trait IntoDecimal {
    fn into_decimal(self) -> i64;
}

impl<'a, I> IntoDecimal for I
where
    I: IntoIterator<Item = &'a u8>,
{
    fn into_decimal(self) -> i64 {
        struct AsInt(i64);

        impl AsInt {
            fn into_decimal(self) -> i64 {
                self.0
            }
        }

        impl std::iter::FromIterator<i64> for AsInt {
            fn from_iter<It: IntoIterator<Item = i64>>(it: It) -> AsInt {
                AsInt(it.into_iter().fold(0, |acc, x| acc * 10 + x))
            }
        }

        self.into_iter()
            .map(|&x| x.into())
            .collect::<AsInt>()
            .into_decimal()
    }
}

fn solve(offset: usize, xs: &[u8], fft: impl Fn(&[u8]) -> Vec<u8>) -> i64 {
    let xs = &xs[offset..];
    std::iter::successors(Some(xs.to_vec()), |xs| Some(fft(xs)))
        .nth(100)
        .unwrap()
        .iter()
        .take(8)
        .into_decimal()
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = read_to_string("input")?
        .trim()
        .chars()
        .map(|c| c.to_digit(10).map(|x| x as u8))
        .collect::<Option<Vec<_>>>()
        .unwrap();

    println!("{}", solve(0, &input, fft));

    let offset = input.iter().take(7).into_decimal() as usize;
    let repeated_input: Vec<_> = std::iter::repeat(input).take(10_000).flatten().collect();

    if offset < repeated_input.len() / 2 {
        panic!(
            "Offset must be smaller than 10_000 * <input_length>, but {} < {}",
            offset,
            repeated_input.len() / 2
        );
    }
    println!("{}", solve(offset, &repeated_input, fft_part2));

    Ok(())
}
