use std::{
    io,
    marker::PhantomData,
    path::Path,
};

use graph::{
    CartesianPoint,
    Point,
    ReadExt,
    RectangularWorld,
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

impl Point for DirectedPoint {
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

impl From<DirectedPoint> for CartesianPoint {
    fn from(value: DirectedPoint) -> Self {
        value.point
    }
}

impl From<CartesianPoint> for DirectedPoint {
    fn from(value: CartesianPoint) -> Self {
        Self {
            point: value,
            direction: (0, 0),
            repeat: 0,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct UltraPoint {
    point: CartesianPoint,
    direction: Direction,
    repeat: usize,
}

impl Point for UltraPoint {
    fn neighbours(self) -> impl Iterator<Item = Self>
    where
        Self: Sized,
    {
        let opposite_direction = (-self.direction.0, -self.direction.1);
        self.point
            .neighbours()
            .map(move |point| {
                let direction = point - self.point;
                let repeat = if direction == self.direction {
                    self.repeat + 1
                }
                else {
                    1
                };
                UltraPoint { point, direction, repeat }
            })
            .filter(move |point| point.direction != opposite_direction)
            .filter(move |point| {
                if self.direction == (0, 0) {
                    true
                }
                else if self.repeat < 4 {
                    point.direction == self.direction
                }
                else if self.repeat == 10 {
                    point.direction != self.direction
                }
                else {
                    true
                }
            })
    }
}

impl From<UltraPoint> for CartesianPoint {
    fn from(value: UltraPoint) -> Self {
        value.point
    }
}

impl From<CartesianPoint> for UltraPoint {
    fn from(value: CartesianPoint) -> Self {
        Self {
            point: value,
            direction: (0, 0),
            repeat: 0,
        }
    }
}

#[derive(Debug, Clone)]
struct Maze<P> {
    map: RectangularWorld<CartesianPoint, Tile>,
    _p: PhantomData<P>,
}

impl Maze<DirectedPoint> {
    fn from_file(filename: impl AsRef<Path>) -> io::Result<Self> {
        Ok(Self {
            map: ReadExt::from_file(filename)?,
            _p: PhantomData,
        })
    }
}

impl<P> graph::World for Maze<P>
where
    P: Point + From<CartesianPoint> + Into<CartesianPoint>,
{
    type Point = P;
    type Tile = Tile;

    fn get(&self, p: &Self::Point) -> Option<Self::Tile> {
        self.map.get(&p.clone().into())
    }

    fn iter(&self) -> impl Iterator<Item = (Self::Point, &Self::Tile)> {
        World::iter(&self.map).map(|(p, t)| (P::from(p), t))
    }

    fn cost(&self, p: &Self::Point) -> u64 {
        self.get(p).unwrap().cost
    }
}

impl From<Maze<DirectedPoint>> for Maze<UltraPoint> {
    fn from(value: Maze<DirectedPoint>) -> Self {
        Maze { map: value.map, _p: PhantomData }
    }
}

fn shortest_path_length<P>(maze: &Maze<P>) -> u64
where
    P: Point + From<CartesianPoint>,
    CartesianPoint: From<P>,
{
    let start = CartesianPoint(0, 0);
    let target = maze
        .iter()
        .map(|(p, _)| CartesianPoint::from(p))
        .max_by_key(|&CartesianPoint(x, y)| (y, x))
        .unwrap();
    let distance = maze.distance_with(&start.into(), |p| CartesianPoint::from(p.clone()) == target);
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

    #[test]
    fn test_part_2() -> io::Result<()> {
        let maze = Maze::<UltraPoint>::from(Maze::from_file("input_test")?);
        assert_eq!(shortest_path_length(&maze), 94);
        Ok(())
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let maze = Maze::from_file("input")?;
    println!("{}", shortest_path_length(&maze));
    let ultra_maze = Maze::<UltraPoint>::from(maze);
    println!("{}", shortest_path_length(&ultra_maze));
    Ok(())
}
