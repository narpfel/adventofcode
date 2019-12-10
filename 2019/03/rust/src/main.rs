use std::io;
use std::fs::read_to_string;
use std::collections::{HashSet, HashMap};
use std::cell::RefCell;
use std::rc::Rc;

type Point = (i64, i64);
type Direction = char;

fn parse_direction(s: &str) -> Result<(Direction, i64), std::num::ParseIntError> {
    let (c, number) = s.split_at(1);
    Ok((c.chars().next().unwrap(), number.parse()?))
}

fn move_(mut p: Point, direction: Direction) -> Point {
    match direction {
        'R' => p.0 += 1,
        'L' => p.0 -= 1,
        'U' => p.1 += 1,
        'D' => p.1 -= 1,
        _ => panic!(),
    };
    p
}

fn manhattan_distance(p: Point) -> u64 {
    p.0.abs() as u64 + p.1.abs() as u64
}

fn track(steps: impl Iterator<Item = (Direction, i64)>) -> HashMap<Point, (u64, usize)> {
    let point = Rc::new(RefCell::new((0, 0)));
    steps.flat_map(|(direction, length)| {
        let direction = direction;
        let point = Rc::clone(&point);
        (0..length).map(move |_| {
            point.replace_with(|p| move_(*p, direction));
            *point.borrow()
        })
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

    let keys = paths.iter()
        .map(|m| m.keys().cloned().collect::<HashSet<Point>>())
        .collect::<Vec<_>>();

    let crossings = keys[0].intersection(&keys[1]).collect::<HashSet<_>>();
    println!(
        "{}",
        crossings.iter().map(|crossing| paths[0][crossing].0).min().unwrap()
    );
    println!(
        "{}",
        crossings.iter().map(|crossing| paths[0][crossing].1 + paths[1][crossing].1).min().unwrap()
    );
    Ok(())
}
