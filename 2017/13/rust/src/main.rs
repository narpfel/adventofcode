use std::{
    collections::HashMap,
    fs::read_to_string,
    path::Path,
};

use failure::Fallible;
use num::Integer;

type Depth = u64;
type Position = u64;
type Time = u64;

type Firewall = HashMap<Position, Depth>;

fn position(depth: Depth, time: Time) -> Position {
    if depth == 0 {
        return 0;
    }

    let (d, m) = time.div_mod_floor(&(depth - 1));

    if d.is_even() {
        m
    }
    else {
        depth - m - 1
    }
}

fn is_caught(depth: Depth, time: Time) -> bool {
    position(depth, time) == 0
}

fn severity(delay: Time, firewall: &Firewall) -> u64 {
    firewall
        .iter()
        .filter(|(&position, &depth)| is_caught(depth, position + delay))
        .map(|(position, depth)| (position + delay) * depth)
        .sum()
}

fn find_delay(firewall: &Firewall) -> Time {
    (0..).find(|&t| severity(t, firewall) == 0).unwrap()
}

fn read_input(path: impl AsRef<Path>) -> Fallible<Firewall> {
    Ok(read_to_string(path)?
        .lines()
        .flat_map(|line| {
            line.split(": ")
                .map(str::parse)
                .collect::<Result<Vec<u64>, _>>()
                .map(|numbers| (numbers[0], numbers[1]))
        })
        .collect())
}

fn main() -> Fallible<()> {
    let firewall = read_input("input")?;

    println!("{}", severity(0, &firewall));
    println!("{}", find_delay(&firewall));
    Ok(())
}
