#![feature(iterator_try_collect)]

use std::error::Error;
use std::path::Path;

use rayon::iter::IntoParallelRefIterator as _;
use rayon::iter::ParallelIterator as _;

type Equation = (u64, Vec<u64>);

fn parse_input(filename: impl AsRef<Path>) -> Result<Vec<Equation>, Box<dyn Error>> {
    std::fs::read_to_string(filename)?
        .lines()
        .map(|line| {
            let (test_value, operands) =
                line.split_once(": ").ok_or("line did not contain colon")?;
            let operands = operands
                .split(' ')
                .map(|operand| operand.parse::<u64>())
                .try_collect()?;
            Ok((test_value.parse()?, operands))
        })
        .collect()
}

fn is_valid_calibration<const N: usize>(
    test_value: u64,
    current: u64,
    operands: &[u64],
    operators: [fn(u64, u64) -> u64; N],
) -> bool {
    match operands {
        [] => test_value == current,
        [operand, operands @ ..] => operators.iter().any(|op| {
            let current = op(current, *operand);
            current <= test_value && is_valid_calibration(test_value, current, operands, operators)
        }),
    }
}

fn calculate_total_calibration_result<const N: usize>(
    input: &[Equation],
    operators: [fn(u64, u64) -> u64; N],
) -> u64 {
    input
        .par_iter()
        .filter(|(test_value, operands)| {
            is_valid_calibration(*test_value, operands[0], &operands[1..], operators)
        })
        .map(|(test_value, _)| test_value)
        .sum()
}

fn part_1(input: &[Equation]) -> u64 {
    calculate_total_calibration_result(input, [|x, y| x + y, |x, y| x * y])
}

fn concat(x: u64, y: u64) -> u64 {
    let mut base = 1;
    while base <= y {
        base *= 10;
    }
    x * base + y
}

fn part_2(input: &[Equation]) -> u64 {
    calculate_total_calibration_result(input, [|x, y| x + y, |x, y| x * y, concat])
}

fn main() -> Result<(), Box<dyn Error>> {
    let input = parse_input("input")?;
    println!("{}", part_1(&input));
    println!("{}", part_2(&input));
    Ok(())
}
