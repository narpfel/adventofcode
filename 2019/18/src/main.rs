#![feature(entry_insert)]

use std::{
    collections::HashMap,
    convert::{
        TryFrom,
        TryInto,
    },
    fs::File,
    io::{
        self,
        BufRead,
        BufReader,
    },
    path::Path,
};

mod graph;

use graph::{
    CartesianPoint as Point,
    World,
};

#[derive(Copy, Clone, PartialEq, Eq, Debug, PartialOrd, Ord)]
enum Tile {
    Wall,
    Empty,
    Key(u32),
    Door(u32),
    Entrance,
}

impl TryFrom<char> for Tile {
    type Error = char;

    fn try_from(c: char) -> Result<Self, Self::Error> {
        use Tile::*;
        Ok(match c {
            '#' => Wall,
            '.' => Empty,
            '@' => Entrance,
            c if c.is_lowercase() => Key(1 << (c as u8 - b'a')),
            c if c.is_uppercase() => Door(1 << (c as u8 - b'A')),
            c => return Err(c),
        })
    }
}

impl graph::Tile for Tile {
    fn is_walkable(&self) -> bool {
        !matches!(self, Tile::Wall)
    }
}

#[derive(Clone, Default, Debug)]
struct Maze {
    maze: HashMap<Point, Tile>,
    adjacency: Vec<Vec<(u64, u32)>>,
}

impl Maze {
    fn new(maze: HashMap<Point, Tile>) -> Self {
        let key_locations: Vec<_> = {
            let mut keys: Vec<_> = maze
                .iter()
                .filter_map(|(point, tile)| match tile {
                    Tile::Entrance | Tile::Key(_) => Some((tile, point)),
                    _ => None,
                })
                .collect();
            keys.sort();
            keys.into_iter().map(|(_, point)| point).collect()
        };
        let mut adjacency =
            vec![vec![Default::default(); key_locations.len()]; key_locations.len()];

        for (i, start) in key_locations.iter().enumerate() {
            for (point, path) in maze.walk_cells_breadth_first(start) {
                if let Some(j) = key_locations
                    .iter()
                    .enumerate()
                    .find_map(|(j, &&p)| if p == point { Some(j) } else { None })
                {
                    adjacency[i][j] = (
                        path.len() as _,
                        path.iter()
                            .filter_map(|point| match maze.get(point) {
                                Some(Tile::Door(mask)) => Some(mask),
                                _ => None,
                            })
                            .fold(0, |acc, mask| acc | mask),
                    );
                }
            }
        }

        Self { maze, adjacency }
    }

    fn key_count(&self) -> usize {
        self.adjacency.len() - 1
    }
}

#[derive(Debug)]
enum Error {
    WrongChar(char),
    IoError(io::Error),
}

impl From<char> for Error {
    fn from(c: char) -> Self {
        Error::WrongChar(c)
    }
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Self {
        Error::IoError(err)
    }
}

fn read_input(path: impl AsRef<Path>) -> Result<Maze, Error> {
    let f = File::open(path)?;
    let reader = BufReader::new(f);

    let mut maze = HashMap::new();
    for (y, line) in reader.lines().enumerate() {
        for (x, c) in line?.chars().enumerate() {
            maze.insert(Point(x, y), c.try_into()?);
        }
    }

    Ok(Maze::new(maze))
}

fn dfs(
    maze: &Maze,
    distance: u64,
    open_doors: u32,
    key: usize,
    collected_keys: usize,
    visited_positions: &mut HashMap<(u32, usize), u64>,
    min_distance: &mut u64,
) -> Option<u64> {
    if collected_keys == maze.key_count() {
        return Some(distance);
    }

    match visited_positions.entry((open_doors, key)) {
        std::collections::hash_map::Entry::Occupied(entry) if *entry.get() <= distance =>
            return None,
        entry => {
            entry.insert(distance);
        }
    }

    let d = maze.adjacency[key][..maze.key_count()]
        .iter()
        .enumerate()
        .filter_map(|(key, (additional_distance, mask))| {
            let distance = distance + additional_distance;
            if distance >= *min_distance {
                return None;
            }
            if open_doors & 1 << key != 0 {
                return None;
            }
            if open_doors & mask == *mask {
                let open_doors = open_doors | 1 << key;
                dfs(
                    maze,
                    distance,
                    open_doors | 1 << key,
                    key,
                    collected_keys + 1,
                    visited_positions,
                    min_distance,
                )
            }
            else {
                None
            }
        })
        .min();

    if let Some(d) = d {
        *min_distance = d;
        Some(d)
    }
    else {
        None
    }
}

fn solve(path: impl AsRef<Path>) -> u64 {
    let maze = read_input(path).unwrap();
    let mut min_distance = u64::MAX;
    dfs(
        &maze,
        0,
        0,
        maze.key_count(),
        0,
        &mut HashMap::default(),
        &mut min_distance,
    )
    .unwrap()
}

#[cfg(test)]
mod tests {
    use super::solve;

    #[test]
    fn test_1() {
        assert_eq!(solve("input_test_1"), 8);
    }

    #[test]
    fn test_2() {
        assert_eq!(solve("input_test_2"), 86);
    }

    #[test]
    fn test_3() {
        assert_eq!(solve("input_test_3"), 132);
    }

    #[test]
    fn test_4() {
        assert_eq!(solve("input_test_4"), 136);
    }

    #[test]
    fn test_5() {
        assert_eq!(solve("input_test_5"), 81);
    }
}

fn main() {
    println!("{}", solve("input"));
}
