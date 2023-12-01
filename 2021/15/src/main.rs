use std::error::Error;

use fnv::FnvHashMap;

use graph::{
    CartesianPoint as Point,
    ReadExt,
    World,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Tile {
    risk_level: u64,
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
            .map(|risk_level| Tile { risk_level: risk_level as _ })
    }
}

#[derive(Debug, Clone)]
struct Cave {
    risk_levels: FnvHashMap<Point, Tile>,
}

impl World for Cave {
    type Point = Point;
    type Tile = Tile;

    fn get(&self, p: &Self::Point) -> Option<Self::Tile> {
        self.risk_levels.get(p).cloned()
    }

    fn iter(&self) -> impl Iterator<Item = (Self::Point, &Self::Tile)> {
        World::iter(&self.risk_levels)
    }

    fn cost(&self, p: &Self::Point) -> u64 {
        self.risk_levels[p].risk_level
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let cave = Cave {
        risk_levels: ReadExt::from_file("input")?,
    };

    let start = Point(0, 0);
    let end = cave.risk_levels.keys().max().unwrap();
    println!("{}", u64::try_from(cave.distance(&start, end)).unwrap());

    let mut real_cave = cave.clone();
    let Point(x, y) = end;
    let (x, y) = (x + 1, y + 1);
    for (point, risk_level) in &cave.risk_levels {
        for j in 0..5 {
            for i in 0..5 {
                if (i, j) == (0, 0) {
                    continue;
                }
                let mut new_risk_level = risk_level.risk_level + i as u64 + j;
                if new_risk_level > 9 {
                    new_risk_level = new_risk_level % 10 + 1;
                }
                real_cave.risk_levels.insert(
                    Point(point.0 + i * x, point.1 + j as usize * y),
                    Tile { risk_level: new_risk_level },
                );
            }
        }
    }

    let end = real_cave.risk_levels.keys().max().unwrap();
    println!(
        "{}",
        u64::try_from(real_cave.distance(&start, end)).unwrap()
    );

    Ok(())
}
