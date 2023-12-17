use std::{
    io,
    path::Path,
};

use fnv::FnvHashMap;
use graph::{
    CartesianPoint,
    ReadExt,
    World,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Tile {
    cost: u64,
}

impl graph::Tile for Tile {
    fn is_walkable(&self) -> bool {
        true
    }
}

impl TryFrom<char> for Tile {
    type Error = char;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        value
            .to_digit(10)
            .ok_or(value)
            .map(|digit| Tile { cost: digit.into() })
    }
}

type Direction = (i64, i64);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct DirectedPoint {
    point: CartesianPoint,
    direction: Direction,
    repeat: usize,
}

impl graph::Point for DirectedPoint {
    fn neighbours(self) -> impl Iterator<Item = Self>
    where
        Self: Sized,
    {
        let opposite_direction = (-self.direction.0, -self.direction.1);
        let neighbours = self.point.neighbours();
        neighbours
            .map(move |point| {
                let direction = point - self.point;
                let repeat = if direction == self.direction {
                    self.repeat + 1
                }
                else {
                    1
                };
                DirectedPoint { point, direction, repeat }
            })
            .filter(move |point| point.direction != opposite_direction)
            .filter(|point| point.repeat <= 3)
    }
}

#[derive(Debug, Clone)]
struct Maze {
    map: FnvHashMap<CartesianPoint, Tile>,
}

impl Maze {
    fn from_file(filename: impl AsRef<Path>) -> io::Result<Self> {
        Ok(Self { map: ReadExt::from_file(filename)? })
    }
}

impl graph::World for Maze {
    type Point = DirectedPoint;
    type Tile = Tile;

    fn get(&self, p: &Self::Point) -> Option<Self::Tile> {
        self.map.get(&p.point).copied()
    }

    fn iter(&self) -> impl Iterator<Item = (Self::Point, &Self::Tile)> {
        World::iter(&self.map)
            .map(|(p, t)| (DirectedPoint { point: p, direction: (0, 0), repeat: 0 }, t))
    }

    fn cost(&self, p: &Self::Point) -> u64 {
        self.get(p).unwrap().cost
    }
}

fn shortest_path_length(maze: &Maze) -> u64 {
    let start = CartesianPoint(0, 0);
    let target = maze
        .iter()
        .map(|(p, _)| p.point)
        .max_by_key(|&CartesianPoint(x, y)| (y, x))
        .unwrap();
    let distance = maze.distance_with(
        &DirectedPoint {
            point: start,
            direction: (0, 0),
            repeat: 0,
        },
        |p| p.point == target,
    );
    distance.try_into().unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_part_1() -> io::Result<()> {
        let maze = Maze::from_file("input_test")?;
        assert_eq!(shortest_path_length(&maze), 102);
        Ok(())
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let maze = Maze::from_file("input")?;
    println!("{}", shortest_path_length(&maze));
    Ok(())
}
