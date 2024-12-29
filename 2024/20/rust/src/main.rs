#![feature(integer_sign_cast)]
#![feature(let_chains)]

use std::io;

use graph::CartesianPoint;
use graph::ReadExt as _;
use graph::RectangularWorld;
use graph::World as _;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Tile {
    Empty,
    Wall,
    Start,
    End,
}

impl graph::Tile for Tile {
    fn is_walkable(&self) -> bool {
        !matches!(self, Tile::Wall)
    }
}

impl TryFrom<char> for Tile {
    type Error = char;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        Ok(match value {
            '.' => Self::Empty,
            '#' => Self::Wall,
            'S' => Self::Start,
            'E' => Self::End,
            _ => return Err(value),
        })
    }
}

fn solve(path: &[CartesianPoint], max_cheat_length: isize) -> usize {
    let xsize = path.iter().map(|&CartesianPoint(x, _)| x).max().unwrap() + 1;
    let ysize = path.iter().map(|&CartesianPoint(_, y)| y).max().unwrap() + 1;
    let mut visited_points = vec![None; xsize * ysize];
    for (i, &CartesianPoint(x, y)) in path.iter().enumerate() {
        visited_points[y * xsize + x] = Some(i);
    }

    let mut possible_cheat_count = 0;
    // FIXME: this can be parallelised
    for (i, &p) in path.iter().enumerate() {
        for dy in -max_cheat_length..max_cheat_length + 1 {
            let x_range = max_cheat_length - dy.abs();
            for dx in -x_range..x_range + 1 {
                let CartesianPoint(x, y) = p + (dx, dy);
                if x < xsize
                    && y < ysize
                    && let Some(Some(j)) = visited_points.get(y * xsize + x)
                    && j.cast_signed() - i.cast_signed() - dx.abs() - dy.abs() >= 100
                {
                    possible_cheat_count += 1;
                }
            }
        }
    }
    possible_cheat_count
}

fn main() -> io::Result<()> {
    let racetrack = RectangularWorld::<CartesianPoint, _>::from_file("input")?;
    let start = racetrack.find(&Tile::Start).unwrap();
    let end = racetrack.find(&Tile::End).unwrap();
    let path = racetrack.path(&start, &end).unwrap();
    println!("{}", solve(&path, 2));
    println!("{}", solve(&path, 20));
    Ok(())
}
