use std::{
    collections::{
        HashMap,
        HashSet,
    },
    fs::read_to_string,
    io,
};

type Point = (i64, i64);

#[derive(Copy, Clone, Debug)]
enum Direction {
    R,
    L,
    U,
    D,
}

use Direction::*;

impl Direction {
    fn from_char(c: char) -> Direction {
        match c {
            'R' => R,
            'L' => L,
            'U' => U,
            'D' => D,
            _ => unreachable!(),
        }
    }
}

fn parse_direction(s: &str) -> Result<(Direction, usize), std::num::ParseIntError> {
    let (c, number) = s.split_at(1);
    Ok((
        Direction::from_char(c.chars().next().unwrap()),
        number.parse()?,
    ))
}

fn move_(p: &mut Point, direction: Direction) {
    match direction {
        R => p.0 += 1,
        L => p.0 -= 1,
        U => p.1 += 1,
        D => p.1 -= 1,
    };
}

fn manhattan_distance(p: Point) -> u64 {
    p.0.unsigned_abs() + p.1.unsigned_abs()
}

fn track(steps: impl Iterator<Item = (Direction, usize)>) -> HashMap<Point, (u64, usize)> {
    steps
        .flat_map(|(direction, length)| std::iter::repeat(direction).take(length))
        .scan((0, 0), |point, direction| {
            move_(point, direction);
            Some(*point)
        })
        .enumerate()
        .map(|(index, p)| (p, (manhattan_distance(p), index + 1)))
        .skip(1)
        .collect()
}

fn main() -> io::Result<()> {
    let paths = read_to_string("input")?
        .lines()
        .map(|line| track(line.split(',').map(parse_direction).filter_map(Result::ok)))
        .collect::<Vec<_>>();

    let keys = paths
        .iter()
        .map(|m| m.keys().cloned().collect::<HashSet<Point>>())
        .collect::<Vec<_>>();

    let crossings = keys[0].intersection(&keys[1]).collect::<HashSet<_>>();
    println!(
        "{}",
        crossings
            .iter()
            .map(|crossing| paths[0][crossing].0)
            .min()
            .unwrap()
    );
    println!(
        "{}",
        crossings
            .iter()
            .map(|crossing| paths[0][crossing].1 + paths[1][crossing].1)
            .min()
            .unwrap()
    );
    Ok(())
}
