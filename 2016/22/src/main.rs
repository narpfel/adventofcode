use std::{
    collections::HashMap,
    hash::{
        BuildHasher,
        Hash,
    },
};

use graph::{
    CartesianPoint as Point,
    ReadExt,
    World,
};

#[derive(Copy, Clone, PartialEq, Eq, Debug, PartialOrd, Ord)]
enum Tile {
    Blocked,
    Full,
    Empty,
    Goal,
}

impl TryFrom<char> for Tile {
    type Error = char;

    fn try_from(c: char) -> Result<Self, Self::Error> {
        use Tile::*;
        Ok(match c {
            '#' => Blocked,
            '.' => Full,
            '_' => Empty,
            'G' => Goal,
            'O' => Full,
            c => return Err(c),
        })
    }
}

impl graph::Tile for Tile {
    fn is_walkable(&self) -> bool {
        !matches!(self, Tile::Blocked | Tile::Goal)
    }
}

fn swap<K, V, H>(map: &mut HashMap<K, V, H>, k1: K, k2: K)
where
    K: Hash + Eq,
    H: BuildHasher,
{
    let v1 = map.remove(&k1).unwrap();
    let v2 = map.remove(&k2).unwrap();
    map.insert(k2, v1);
    map.insert(k1, v2);
}

fn main() {
    let mut grid = HashMap::from_file("grid").unwrap();
    let goal = grid.find(&Tile::Goal).unwrap();
    let goal_path = grid.path(&goal, &Point(0, 0)).unwrap();

    let distance: u64 = goal_path
        .into_iter()
        .skip(1)
        .map(|target_for_empty| {
            let goal = grid.find(&Tile::Goal).unwrap();
            let empty = grid.find(&Tile::Empty).unwrap();
            let distance_to_target_for_empty: u64 =
                grid.distance(&empty, &target_for_empty).try_into().unwrap();
            swap(&mut grid, empty, target_for_empty);
            swap(&mut grid, target_for_empty, goal);
            distance_to_target_for_empty + 1
        })
        .sum();

    println!("{}", distance);
}
