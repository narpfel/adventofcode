use std::collections::HashMap;

use graph::{
    CartesianPoint as Point,
    ReadExt,
    World,
};

#[derive(Copy, Clone, PartialEq, Eq, Debug, PartialOrd, Ord)]
struct Tile {
    height: u8,
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
            .map(|height| Tile { height: height as u8 })
    }
}

fn main() {
    let height_map: HashMap<Point, Tile, _> = HashMap::from_file("input").unwrap();
    let risk_level = height_map
        .iter()
        .map(|(&point, &tile)| {
            if height_map
                .neighbours(point)
                .all(|neighbour| height_map[&neighbour] > tile)
            {
                usize::from(tile.height) + 1
            }
            else {
                0
            }
        })
        .sum::<usize>();
    println!("{}", risk_level);
}
