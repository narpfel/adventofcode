use std::{
    error::Error,
    fs::read_to_string,
};

fn fuel_consumption_part_1(start: u64, end: u64) -> u64 {
    start.abs_diff(end)
}

fn fuel_consumption_part_2(start: u64, end: u64) -> u64 {
    let distance = start.abs_diff(end);
    distance * (distance + 1) / 2
}

fn main() -> Result<(), Box<dyn Error>> {
    let positions = read_to_string("input")?
        .trim()
        .split(',')
        .map(str::parse)
        .collect::<Result<Vec<_>, _>>()?;

    let min = *positions.iter().min().unwrap();
    let max = *positions.iter().max().unwrap();
    for fuel_consumption in [fuel_consumption_part_1, fuel_consumption_part_2] {
        println!(
            "{}",
            (min..=max)
                .map(|destination| positions
                    .iter()
                    .map(|&position| fuel_consumption(destination, position))
                    .sum::<u64>())
                .min()
                .unwrap()
        );
    }
    Ok(())
}
