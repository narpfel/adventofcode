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
struct Map {
    map: FnvHashMap<CartesianPoint, Tile>,
}

impl World for Map {
    type Point = CartesianPoint;
    type Tile = Tile;

    fn get(&self, p: &Self::Point) -> Option<Self::Tile> {
        World::get(&self.map, p)
    }

    fn find(&self, tile: &Self::Tile) -> Option<Self::Point> {
        self.map.find(tile)
    }

    fn neighbours<'a>(&'a self, point: Self::Point) -> Box<dyn Iterator<Item = Self::Point> + 'a> {
        let max_height = self.map[&point].height() + 1;
        Box::new(
            self.map
                .neighbours(point)
                .filter(move |p| max_height >= self.map[p].height()),
        )
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let map = Map { map: FnvHashMap::from_file("input")? };
    let start = map.find(&Tile::Start).unwrap();
    let end = map.find(&Tile::Destination).unwrap();
    let part_1 = u64::try_from(map.distance(&start, &end)).unwrap();
    println!("{part_1}");
    Ok(())
}
