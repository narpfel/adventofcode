#![feature(entry_insert)]
#![feature(thread_local)]

use std::{
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
    iter::from_fn,
    path::Path,
};

use fnv::FnvHashMap;

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
    maze: FnvHashMap<Point, Tile>,
    adjacency: Vec<Vec<Option<(u64, u32)>>>,
    entrance_count: usize,
}

impl Maze {
    fn new(maze: FnvHashMap<Point, Tile>) -> Self {
        let entrance_count;
        let key_locations: Vec<_> = {
            let mut keys: Vec<_> = maze
                .iter()
                .filter_map(|(point, tile)| match tile {
                    Tile::Entrance | Tile::Key(_) => Some((tile, point)),
                    _ => None,
                })
                .collect();
            keys.sort();
            entrance_count = keys
                .iter()
                .rev()
                .take_while(|(tile, _)| matches!(tile, Tile::Entrance))
                .count();
            keys.into_iter().map(|(_, point)| point).collect()
        };
        let location_to_key: FnvHashMap<_, _> = key_locations
            .iter()
            .enumerate()
            .map(|(key, point)| (*point, key))
            .collect();
        let mut adjacency =
            vec![vec![Default::default(); key_locations.len()]; key_locations.len()];

        for (i, start) in key_locations.iter().enumerate() {
            for (point, path) in maze.walk_cells_breadth_first(start) {
                if let Some(&j) = location_to_key.get(&point) {
                    adjacency[i][j] = Some((
                        path.len() as _,
                        path.iter()
                            .filter_map(|point| match maze.get(point) {
                                Some(Tile::Door(mask)) => Some(mask),
                                _ => None,
                            })
                            .fold(0, |acc, mask| acc | mask),
                    ));
                }
            }
        }

        Self { maze, adjacency, entrance_count }
    }

    fn key_count(&self) -> usize {
        self.adjacency.len() - self.entrance_count
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

fn read_input(path: impl AsRef<Path>) -> Result<FnvHashMap<Point, Tile>, Error> {
    let f = File::open(path)?;
    let reader = BufReader::new(f);

    let mut maze = FnvHashMap::default();
    for (y, line) in reader.lines().enumerate() {
        for (x, c) in line?.chars().enumerate() {
            maze.insert(Point(x, y), c.try_into()?);
        }
    }

    Ok(maze)
}

fn dfs(
    maze: &Maze,
    distance: u64,
    open_doors: u32,
    positions: u32,
    collected_keys: usize,
    visited_positions: &mut FnvHashMap<(u32, u32), u64>,
    min_distance: &mut u64,
) -> Option<u64> {
    if collected_keys == maze.key_count() {
        return Some(distance);
    }

    match visited_positions.entry((open_doors, positions)) {
        std::collections::hash_map::Entry::Occupied(entry) if *entry.get() <= distance =>
            return None,
        entry => {
            entry.insert(distance);
        }
    }

    let d = iter_set_bits(positions)
        .flat_map(|position| {
            maze.adjacency[position as usize][..maze.key_count()]
                .iter()
                .enumerate()
                .filter_map(|(i, opt)| opt.map(|val| (i, val)))
                .filter_map(|(key, (additional_distance, mask))| {
                    let key = 1 << key;
                    let distance = distance + additional_distance;
                    if distance >= *min_distance {
                        return None;
                    }
                    if open_doors & key != 0 {
                        return None;
                    }
                    if open_doors & mask == mask {
                        let positions = (positions & !(1 << position)) | key;
                        dfs(
                            maze,
                            distance,
                            open_doors | key,
                            positions,
                            collected_keys + 1,
                            visited_positions,
                            min_distance,
                        )
                    }
                    else {
                        None
                    }
                })
                .min()
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

fn find_path_length(maze: &Maze) -> u64 {
    dfs(
        maze,
        0,
        0,
        (maze.key_count()..maze.key_count() + maze.entrance_count)
            .map(|i| 1 << i)
            .fold(0, std::ops::BitOr::bitor),
        0,
        &mut FnvHashMap::default(),
        &mut { u64::MAX },
    )
    .unwrap()
}

fn solve_part_1(maze: &Maze) -> u64 {
    find_path_length(maze)
}

fn solve_part_2(maze: &Maze) -> u64 {
    const REPLACEMENT: [[Tile; 3]; 3] = [
        [Tile::Entrance, Tile::Wall, Tile::Entrance],
        [Tile::Wall, Tile::Wall, Tile::Wall],
        [Tile::Entrance, Tile::Wall, Tile::Entrance],
    ];
    let bottom_right_tile = *maze
        .maze
        .keys()
        .max_by_key(|tile| (tile.1, tile.0))
        .unwrap();
    let maze = {
        let mut maze = maze.maze.clone();
        IntoIterator::into_iter(REPLACEMENT)
            .enumerate()
            .for_each(|(dy, tiles)| {
                IntoIterator::into_iter(tiles)
                    .enumerate()
                    .for_each(|(dx, tile)| {
                        maze.insert(
                            Point(
                                bottom_right_tile.0 / 2 + dx - 1,
                                bottom_right_tile.1 / 2 + dy - 1,
                            ),
                            tile,
                        );
                    })
            });
        Maze::new(maze)
    };

    find_path_length(&maze)
}

fn iter_set_bits(mut x: u32) -> impl Iterator<Item = u32> {
    from_fn(move || {
        if x == 0 {
            None
        }
        else {
            let i = x.trailing_zeros();
            x ^= 1 << i;
            Some(i)
        }
    })
}

#[cfg(test)]
mod tests {
    use super::{
        iter_set_bits,
        read_input,
        solve_part_1,
        solve_part_2,
        Maze,
    };

    #[test]
    fn test_1() {
        assert_eq!(
            solve_part_1(&Maze::new(read_input("input_test_1").unwrap())),
            8
        );
    }

    #[test]
    fn test_2() {
        assert_eq!(
            solve_part_1(&Maze::new(read_input("input_test_2").unwrap())),
            86
        );
    }

    #[test]
    fn test_3() {
        assert_eq!(
            solve_part_1(&Maze::new(read_input("input_test_3").unwrap())),
            132
        );
    }

    #[test]
    fn test_4() {
        assert_eq!(
            solve_part_1(&Maze::new(read_input("input_test_4").unwrap())),
            136
        );
    }

    #[test]
    fn test_5() {
        assert_eq!(
            solve_part_1(&Maze::new(read_input("input_test_5").unwrap())),
            81
        );
    }

    #[test]
    fn test_part_2_1() {
        assert_eq!(
            solve_part_2(&Maze::new(read_input("input_test_part_2_1").unwrap())),
            8
        );
    }

    #[test]
    fn test_part_2_2() {
        assert_eq!(
            solve_part_2(&Maze::new(read_input("input_test_part_2_2").unwrap())),
            24
        );
    }

    #[test]
    fn test_part_2_3() {
        assert_eq!(
            solve_part_2(&Maze::new(read_input("input_test_part_2_3").unwrap())),
            32
        );
    }

    #[test]
    fn test_part_2_4() {
        assert_eq!(
            solve_part_2(&Maze::new(read_input("input_test_part_2_4").unwrap())),
            72
        );
    }

    #[test]
    fn test_iter_set_bits() {
        assert_eq!(iter_set_bits(0b100101).collect::<Vec<_>>(), vec![0, 2, 5]);
    }
}

fn main() {
    let maze = Maze::new(read_input("input").unwrap());
    println!("{}", solve_part_1(&maze));
    println!("{}", solve_part_2(&maze));
}
