use std::io;
use std::marker::PhantomData;
use std::num::Wrapping;
use std::path::Path;

use graph::CartesianPoint;
use graph::Distance;
use graph::MonotonicPriorityQueue;
use graph::ReadExt;
use graph::RectangularWorld;
use graph::World;

trait Point: graph::Point + From<CartesianPoint> + Into<CartesianPoint> {
    fn repeat(&self) -> u16;
    fn direction(&self) -> usize;
}

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
    fn repeat(&self) -> u16 {
        self.repeat as _
    }

    fn direction(&self) -> usize {
        let (x, y) = self.direction;
        let x = Wrapping(x as u64);
        let y = Wrapping(y as u64);
        ((x - Wrapping(3) * y + Wrapping(3)) / Wrapping(2)).0 as _
    }
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

impl graph::Point for UltraPoint {
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
                // TODO: Use const generics for 4 and 10, unifying both point types
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

impl Point for UltraPoint {
    fn repeat(&self) -> u16 {
        self.repeat as _
    }

    fn direction(&self) -> usize {
        let (x, y) = self.direction;
        let x = Wrapping(x as u64);
        let y = Wrapping(y as u64);
        ((x - Wrapping(3) * y + Wrapping(3)) / Wrapping(2)).0 as _
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
struct City<P> {
    blocks: RectangularWorld<CartesianPoint, Tile>,
    _p: PhantomData<P>,
}

impl City<DirectedPoint> {
    fn from_file(filename: impl AsRef<Path>) -> io::Result<Self> {
        Ok(Self {
            blocks: ReadExt::from_file(filename)?,
            _p: PhantomData,
        })
    }
}

impl<P> City<P>
where
    P: Point,
{
    fn index(&self, point: &<City<P> as World>::Point) -> usize {
        self.blocks.index(&point.clone().into())
    }
}

impl From<City<DirectedPoint>> for City<UltraPoint> {
    fn from(value: City<DirectedPoint>) -> Self {
        City { blocks: value.blocks, _p: PhantomData }
    }
}

impl<P> graph::World for City<P>
where
    P: Point,
{
    type Point = P;
    type Tile = Tile;

    fn get(&self, p: &Self::Point) -> Option<Self::Tile> {
        self.blocks.get(&p.clone().into())
    }

    fn iter(&self) -> impl Iterator<Item = (Self::Point, &Self::Tile)> {
        World::iter(&self.blocks).map(|(p, t)| (P::from(p), t))
    }

    fn cost(&self, _from: &Self::Point, p: &Self::Point) -> u64 {
        self.get(p).unwrap().cost
    }

    fn distance_with(
        &self,
        start: &Self::Point,
        mut is_at_end: impl FnMut(&Self::Point) -> bool,
    ) -> Distance {
        let mut seen = vec![[0_u16; 4]; self.blocks.len()];
        seen[self.index(start)][start.direction()] |= 1 << start.repeat();

        let mut next_points = MonotonicPriorityQueue::<Self::PointOrder, Self::Point>::new();
        next_points.push(0, start.clone());

        while let Some((distance, point)) = next_points.pop() {
            if is_at_end(&point) {
                return Distance::new(distance);
            }

            for neighbour in self
                .neighbours(point.clone())
                .filter(|neighbour| self.is_walkable(neighbour))
            {
                let distance = distance + self.cost(&point, &neighbour);

                let bitset = &mut seen[self.index(&neighbour)][neighbour.direction()];
                if (*bitset & (1 << neighbour.repeat())) == 0 {
                    *bitset |= 1 << neighbour.repeat();
                    next_points.push(distance, neighbour);
                }
            }
        }

        Distance::infinity()
    }
}

fn shortest_path_length<P>(city: &City<P>, end_point_constraint: impl Fn(&P) -> bool) -> u64
where
    P: Point,
{
    let start = CartesianPoint(0, 0);
    let target = city
        .iter()
        .map(|(p, _)| p.clone().into())
        .max_by_key(|&CartesianPoint(x, y)| (y, x))
        .unwrap();
    let distance = city.distance_with(&start.into(), |p| {
        end_point_constraint(p) && p.clone().into() == target
    });
    distance.try_into().unwrap()
}

fn shortest_path_length_part_1(city: &City<DirectedPoint>) -> u64 {
    shortest_path_length(city, |_| true)
}

fn shortest_path_length_part_2(city: &City<UltraPoint>) -> u64 {
    shortest_path_length(city, |p| (4..11).contains(&p.repeat))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_part_1() -> io::Result<()> {
        let city = City::from_file("input_test")?;
        assert_eq!(shortest_path_length_part_1(&city), 102);
        Ok(())
    }

    #[test]
    fn test_part_2() -> io::Result<()> {
        let city = City::from(City::from_file("input_test")?);
        assert_eq!(shortest_path_length_part_2(&city), 94);
        Ok(())
    }

    #[test]
    fn test_part_2_2() -> io::Result<()> {
        let city = City::from(City::from_file("input_test_2")?);
        assert_eq!(shortest_path_length_part_2(&city), 71);
        Ok(())
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let city = City::from_file("input")?;
    println!("{}", shortest_path_length_part_1(&city));
    let ultra_city = City::from(city);
    println!("{}", shortest_path_length_part_2(&ultra_city));
    Ok(())
}
