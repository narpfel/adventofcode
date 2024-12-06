use std::io;

use fnv::FnvHashSet;
use rayon::iter::IntoParallelIterator as _;
use rayon::iter::ParallelIterator as _;

const DIRECTIONS: [(isize, isize); 4] = [(0, -1), (1, 0), (0, 1), (-1, 0)];

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Tile {
    Start,
    Blocked,
    Empty,
}

impl TryFrom<char> for Tile {
    type Error = char;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        match value {
            '^' => Ok(Tile::Start),
            '#' => Ok(Tile::Blocked),
            '.' => Ok(Tile::Empty),
            _ => Err(value),
        }
    }
}

fn parse_input(filename: impl AsRef<std::path::Path>) -> io::Result<Vec<Vec<Tile>>> {
    let input = std::fs::read_to_string(filename)?;
    Ok(input
        .lines()
        .map(|line| {
            line.trim()
                .chars()
                .map(|c| Tile::try_from(c).unwrap())
                .collect()
        })
        .collect())
}

fn move_(x: usize, y: usize, (dx, dy): (isize, isize)) -> (usize, usize) {
    (x.wrapping_add_signed(dx), y.wrapping_add_signed(dy))
}

type Path = FnvHashSet<(u8, u8, (i8, i8))>;

#[derive(Debug, Clone, Copy)]
struct HasLoop;

fn find_path(tiles: Vec<Vec<Tile>>, start: (usize, usize)) -> Result<Path, HasLoop> {
    let mut directions = DIRECTIONS.into_iter().cycle();
    let mut direction = directions.next().unwrap();
    let mut visited = FnvHashSet::default();
    visited.reserve(10_000);
    let (mut x, mut y) = start;
    loop {
        let inserted = visited.insert((x as u8, y as u8, (direction.0 as i8, direction.1 as i8)));
        if !inserted {
            return Err(HasLoop);
        }

        let (mut nx, mut ny) = move_(x, y, direction);
        (x, y) = loop {
            match tiles.get(ny).and_then(|line| line.get(nx)) {
                Some(Tile::Blocked) => {
                    direction = directions.next().unwrap();
                    (nx, ny) = move_(x, y, direction);
                }
                Some(_) => break (nx, ny),
                None => return Ok(visited),
            }
        };
    }
}

fn part_1(tiles: Vec<Vec<Tile>>, start: (usize, usize)) -> usize {
    find_path(tiles, start)
        .unwrap()
        .iter()
        .map(|(x, y, _)| (x, y))
        .collect::<FnvHashSet<_>>()
        .len()
}

fn has_loop(
    mut tiles: Vec<Vec<Tile>>,
    start: (usize, usize),
    block_x: usize,
    block_y: usize,
) -> bool {
    tiles[block_y][block_x] = Tile::Blocked;
    find_path(tiles, start).is_err()
}

fn part_2(tiles: Vec<Vec<Tile>>, start: (usize, usize)) -> usize {
    find_path(tiles.clone(), start)
        .unwrap()
        .into_iter()
        .map(|(x, y, _)| (x, y))
        .collect::<FnvHashSet<_>>()
        .into_par_iter()
        .filter(|&(x, y)| {
            tiles[usize::from(y)][usize::from(x)] == Tile::Empty
                && has_loop(tiles.clone(), start, x.into(), y.into())
        })
        .count()
}

fn main() -> io::Result<()> {
    let tiles = parse_input("input")?;
    let start = tiles
        .iter()
        .enumerate()
        .find_map(|(y, line)| {
            line.iter()
                .enumerate()
                .find_map(|(x, &tile)| (tile == Tile::Start).then_some((x, y)))
        })
        .unwrap();
    println!("{}", part_1(tiles.clone(), start));
    println!("{}", part_2(tiles, start));
    Ok(())
}
