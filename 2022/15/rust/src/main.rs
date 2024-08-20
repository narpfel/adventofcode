#![feature(array_chunks)]

use std::collections::HashSet;
use std::error::Error;
use std::fs::File;
use std::io::BufRead;
use std::io::BufReader;
use std::path::Path;

use regex::Regex;

trait Succ {
    fn succ(&self) -> Self;
}

impl Succ for i64 {
    fn succ(&self) -> Self {
        self + 1
    }
}

#[derive(Debug)]
struct Sparse<T>(Vec<T>, Vec<T>);

impl<T> Sparse<T> {
    fn new() -> Self {
        Sparse(Vec::with_capacity(32), Vec::with_capacity(32))
    }

    fn clear(&mut self) {
        self.0.clear();
        self.1.clear();
    }
}

impl<T> Sparse<T>
where
    T: Ord,
{
    fn insert(&mut self, (lo, hi): (T, T))
    where
        T: Clone,
    {
        std::mem::swap(&mut self.0, &mut self.1);
        self.0.clear();
        let mut i = 0;
        let mut j = 0;
        for (n, x) in self.1.iter().enumerate() {
            if x < &lo {
                i = n + 1;
            }
            if x <= &hi {
                j = n + 1;
            }
            else {
                break;
            }
        }
        self.0.extend_from_slice(&self.1[..i]);
        if i % 2 == 0 && j % 2 == 0 {
            self.0.extend_from_slice(&[lo, hi]);
        }
        else if i % 2 == 0 && j % 2 != 0 {
            self.0.push(lo);
        }
        else if i % 2 != 0 && j % 2 == 0 {
            self.0.push(hi);
        }
        self.0.extend_from_slice(&self.1[j..]);
    }

    fn compactify(&mut self)
    where
        T: Clone + Succ,
    {
        if self.0.is_empty() {
            return;
        }
        let mut values = std::mem::take(&mut self.0);
        let last = values.pop().unwrap();
        self.0.push(values[0].clone());
        let mut chunks = values[1..].array_chunks();
        for [x, y] in &mut chunks {
            if y != &x.succ() {
                self.0.push(x.clone());
                self.0.push(y.clone());
            }
        }
        assert!(chunks.remainder().is_empty());
        self.0.push(last);
    }
}

impl Sparse<i64> {
    fn length(&self) -> i64 {
        self.0.array_chunks().map(|[lo, hi]| hi - (lo - 1)).sum()
    }

    fn contains(&self, value: i64) -> bool {
        self.0
            .array_chunks()
            .any(|[lo, hi]| (lo..=hi).contains(&&value))
    }
}

type Coords = Vec<((i64, i64), (i64, i64))>;

fn read_input(filename: impl AsRef<Path>) -> Result<Coords, Box<dyn Error>> {
    let sensor_re = Regex::new(concat!(
        r"Sensor at x=(?P<sensor_x>-?\d+), y=(?P<sensor_y>-?\d+): ",
        r"closest beacon is at x=(?P<beacon_x>-?\d+), y=(?P<beacon_y>-?\d+)",
    ))?;

    let input = File::open(filename)?;
    let input = BufReader::new(input);

    input
        .lines()
        .map(|line| {
            let line = line?;
            let captures = sensor_re
                .captures(&line)
                .ok_or_else(|| format!("no match: {line:?}"))?;
            Ok((
                (captures["sensor_x"].parse()?, captures["sensor_y"].parse()?),
                (captures["beacon_x"].parse()?, captures["beacon_y"].parse()?),
            ))
        })
        .collect()
}

#[inline(always)]
fn blocked_in_line(coords: &Coords, target_y: i64, blocked: &mut Sparse<i64>) {
    blocked.clear();
    for &((sx, sy), (bx, by)) in coords {
        let sensor_range = (sx - bx).abs() + (sy - by).abs();
        let distance = (target_y - sy).abs();
        if distance <= sensor_range {
            let line_length = (sensor_range - distance) * 2 + 1;
            blocked.insert((sx - line_length / 2, sx + line_length / 2));
        }
    }
}

fn part_1(coords: &Coords, target_y: i64) -> i64 {
    let blocked = {
        let mut blocked = Sparse::new();
        blocked_in_line(coords, target_y, &mut blocked);
        blocked.compactify();
        blocked
    };
    let blocked_position_count = blocked.length();
    blocked_position_count
        - i64::try_from(
            coords
                .iter()
                .filter_map(|&(_, (x, y))| (y == target_y && blocked.contains(x)).then_some(x))
                .collect::<HashSet<_>>()
                .len(),
        )
        .unwrap()
}

fn part_2(coords: &Coords, max_y: i64) -> i64 {
    let mut blocked = Sparse::new();
    for y in 0..max_y {
        blocked_in_line(coords, y, &mut blocked);
        if (blocked.0.len() / 2) % 2 == 0 {
            blocked.compactify();
            let x = blocked.0[1] + 1;
            return x * 4_000_000 + y;
        }
    }
    unreachable!()
}

fn main() -> Result<(), Box<dyn Error>> {
    let input = read_input("input")?;
    println!("{}", part_1(&input, 2_000_000));
    println!("{}", part_2(&input, 4_000_000));
    Ok(())
}
