use std::{
    fs::read_to_string,
    io,
    path::Path,
};

type Depth = u64;
type Position = u64;
type Time = u64;

fn position(depth: Depth, time: Time) -> Position {
    if depth == 0 {
        return 0;
    }

    let (div, r#mod) = (time / (depth - 1), time % (depth - 1));

    if div % 2 == 0 {
        r#mod
    }
    else {
        depth - r#mod - 1
    }
}

fn is_caught(depth: Depth, time: Time) -> bool {
    position(depth, time) == 0
}

fn caught_positions(
    time: Time,
    firewall: &[Option<Depth>],
) -> impl Iterator<Item = (u64, u64)> + '_ {
    firewall
        .iter()
        .enumerate()
        .filter_map(|(idx, &opt)| Some((idx as u64, opt?)))
        .filter(move |(position, depth)| is_caught(*depth, time + position))
}

fn severity(delay: Time, firewall: &[Option<Depth>]) -> u64 {
    caught_positions(delay, firewall)
        .map(|(position, depth)| (position + delay) * depth)
        .sum()
}

fn find_delay(firewall: &[Option<Depth>]) -> Time {
    (0..)
        .find(|&time| caught_positions(time, firewall).next().is_none())
        .unwrap()
}

fn read_input(path: impl AsRef<Path>) -> io::Result<Vec<Option<Depth>>> {
    let numbers: Vec<_> = read_to_string(path)?
        .lines()
        .flat_map(|line| {
            line.split(": ")
                .map(str::parse)
                .collect::<Result<Vec<u64>, _>>()
                .map(|numbers| (numbers[0], numbers[1]))
        })
        .collect();

    let mut result = vec![None; numbers.last().unwrap().0 as usize + 1];
    for (idx, n) in numbers {
        result[idx as usize] = Some(n);
    }
    Ok(result)
}

fn main() -> io::Result<()> {
    let firewall = read_input("input")?;

    println!("{}", severity(0, &firewall));
    println!("{}", find_delay(&firewall));
    Ok(())
}
