use std::error::Error;

use fnv::FnvHashMap;
use graph::{
    CartesianPoint,
    ReadExt,
    World,
};

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum Tile {
    Start,
    Destination,
    Tile(u64),
}

#[derive(Debug)]
struct Invalid(char);

impl Tile {
    fn height(self) -> u64 {
        match self {
            Tile::Start => 0,
            Tile::Destination => Tile::try_from('z').unwrap().height(),
            Tile::Tile(height) => height,
        }
    }
}

impl graph::Tile for Tile {
    fn is_walkable(&self) -> bool {
        true
    }
}

impl TryFrom<char> for Tile {
    type Error = Invalid;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        if value.is_ascii_lowercase() {
            Ok(Tile::Tile((value as u32 - 'a' as u32).into()))
        }
        else if value == 'S' {
            Ok(Tile::Start)
        }
        else if value == 'E' {
            Ok(Tile::Destination)
        }
        else {
            Err(Invalid(value))
        }
    }
}

#[derive(Debug, Clone)]
struct Map<F: Clone + Fn(Tile, Tile) -> bool> {
    map: FnvHashMap<CartesianPoint, Tile>,
    can_walk: F,
}

impl<F> World for Map<F>
where
    F: Clone + Fn(Tile, Tile) -> bool,
{
    type Point = CartesianPoint;
    type Tile = Tile;

    fn get(&self, p: &Self::Point) -> Option<Self::Tile> {
        World::get(&self.map, p)
    }

    fn iter(&self) -> Box<dyn Iterator<Item = (Self::Point, &Self::Tile)> + '_> {
        World::iter(&self.map)
    }

    fn neighbours<'a>(&'a self, point: Self::Point) -> Box<dyn Iterator<Item = Self::Point> + 'a> {
        let tile = self.map[&point];
        Box::new(
            self.map
                .neighbours(point)
                .filter(move |p| (self.can_walk)(tile, self.map[p])),
        )
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let map = Map {
        map: FnvHashMap::from_file("input")?,
        can_walk: |a, b| a.height() + 1 >= b.height(),
    };
    let start = map.find(&Tile::Start).unwrap();
    let end = map.find(&Tile::Destination).unwrap();
    let part_1 = u64::try_from(map.distance(&start, &end)).unwrap();
    println!("{part_1}");
    let map = Map {
        map: map.map,
        can_walk: |a, b| a.height() <= b.height() + 1,
    };
    println!(
        "{}",
        u64::try_from(
            map.distance_with(&end, |p| map.get(p) == Some(Tile::try_from('a').unwrap()))
        )
        .unwrap(),
    );
    Ok(())
}
