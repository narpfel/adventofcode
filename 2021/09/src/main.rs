use std::{
    cmp::Reverse,
    collections::HashMap,
};

use graph::{
    CartesianPoint as Point,
    ReadExt,
    Tile as _,
    World,
};

#[derive(Copy, Clone, PartialEq, Eq, Debug, PartialOrd, Ord)]
struct Tile {
    height: u8,
}

impl graph::Tile for Tile {
    fn is_walkable(&self) -> bool {
        self.height < 9
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
    let low_points: Vec<_> = height_map
        .iter()
        .filter_map(|(&point, &tile)| {
            if tile.is_walkable()
                && height_map
                    .neighbours(point)
                    .all(|neighbour| height_map[&neighbour] > tile)
            {
                Some(point)
            }
            else {
                None
            }
        })
        .collect();
    let total_risk_level = low_points
        .iter()
        .map(|point| usize::from(height_map[point].height) + 1)
        .sum::<usize>();
    let mut region_sizes: Vec<_> = low_points
        .iter()
        .map(|point| height_map.walk_cells_breadth_first(point).count() as u64)
        .collect();
    region_sizes.sort_by_key(|&size| Reverse(size));
    println!("{}", total_risk_level);
    println!("{}", region_sizes[0] * region_sizes[1] * region_sizes[2]);
}
