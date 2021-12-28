use std::{
    collections::HashMap,
    hash::BuildHasher,
    iter::{
        empty,
        once,
    },
};

use itertools::Itertools;

use graph::{
    CartesianPoint as Point,
    ReadExt,
    World,
};

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum Tile {
    Wall,
    Empty,
    Robot(u8),
}

impl TryFrom<char> for Tile {
    type Error = char;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        match value {
            '#' => Ok(Tile::Wall),
            '.' => Ok(Tile::Empty),
            c => Ok(Tile::Robot(c.to_digit(10).ok_or(c)? as _)),
        }
    }
}

impl graph::Tile for Tile {
    fn is_walkable(&self) -> bool {
        !matches!(self, Tile::Wall)
    }
}

fn solve(
    maze: &HashMap<Point, Tile, impl BuildHasher + Clone>,
    rest: impl Iterator<Item = Point> + Clone,
) -> u64 {
    let start_point = maze.find(&Tile::Robot(0)).unwrap();
    let robots: Vec<_> = (1..).map_while(|i| maze.find(&Tile::Robot(i))).collect();
    let robot_count = robots.len();

    let distances: HashMap<_, _> = once(start_point)
        .chain(robots.clone())
        .permutations(2)
        .map(|points| {
            (
                (points[0], points[1]),
                u64::try_from(maze.distance(&points[0], &points[1])).unwrap(),
            )
        })
        .collect();

    robots
        .into_iter()
        .permutations(robot_count)
        .map(|rs| once(start_point).chain(rs).chain(rest.clone()))
        .map(|points| {
            points
                .tuple_windows()
                .map(|points| distances[&points])
                .sum()
        })
        .min()
        .unwrap()
}

fn main() {
    let maze = HashMap::from_file("input").unwrap();
    println!("{}", solve(&maze, empty()));
    println!(
        "{}",
        solve(&maze, once(maze.find(&Tile::Robot(0)).unwrap()))
    );
}
