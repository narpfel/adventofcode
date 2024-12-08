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

type Path = FnvHashSet<(usize, usize)>;

#[derive(Debug, Clone, Copy)]
struct HasLoop;

fn find_path(
    visited: &mut [bool],
    tiles: Vec<Vec<Tile>>,
    start: (usize, usize),
) -> Result<impl FnOnce() -> Path + use<'_>, HasLoop> {
    let y_len = tiles.len();
    let x_len = tiles[0].len();

    #[inline(never)]
    fn assert_dimensions_fit_u8(y_len: usize, x_len: usize) {
        assert!(y_len < u8::MAX.into());
        assert!(x_len < u8::MAX.into());
    }
    assert_dimensions_fit_u8(y_len, x_len);

    let mut directions = DIRECTIONS.into_iter().enumerate().cycle();
    let (mut direction_index, mut direction) = directions.next().unwrap();
    let (mut x, mut y) = start;
    loop {
        match visited.get_mut(
            x as u8 as usize * y_len * DIRECTIONS.len()
                + y as u8 as usize * DIRECTIONS.len()
                + direction_index,
        ) {
            Some(was_here @ false) => *was_here = true,
            Some(true) => return Err(HasLoop),
            None => unreachable!(),
        }

        let (mut nx, mut ny) = move_(x, y, direction);
        (x, y) = loop {
            match tiles.get(ny).and_then(|line| line.get(nx)) {
                Some(Tile::Blocked) => {
                    (direction_index, direction) = directions.next().unwrap();
                    (nx, ny) = move_(x, y, direction);
                }
                Some(_) => break (nx, ny),
                None =>
                    return Ok(move || {
                        visited
                            .iter()
                            .enumerate()
                            .filter(|(_, was_visited)| **was_visited)
                            .map(|(i, _)| {
                                (i / (y_len * DIRECTIONS.len()), i / DIRECTIONS.len() % y_len)
                            })
                            .collect()
                    }),
            }
        };
    }
}

fn part_1(tiles: Vec<Vec<Tile>>, start: (usize, usize)) -> usize {
    let y_len = tiles.len();
    let x_len = tiles[0].len();
    find_path(
        &mut vec![false; x_len * y_len * DIRECTIONS.len()],
        tiles,
        start,
    )
    .unwrap()()
    .len()
}

fn has_loop(
    visited: &mut [bool],
    mut tiles: Vec<Vec<Tile>>,
    start: (usize, usize),
    block_x: usize,
    block_y: usize,
) -> bool {
    tiles[block_y][block_x] = Tile::Blocked;
    find_path(visited, tiles, start).is_err()
}

fn part_2(tiles: Vec<Vec<Tile>>, start: (usize, usize)) -> usize {
    let y_len = tiles.len();
    let x_len = tiles[0].len();
    find_path(
        &mut vec![false; x_len * y_len * DIRECTIONS.len()],
        tiles.clone(),
        start,
    )
    .unwrap()()
    .into_par_iter()
    .map_init(
        || vec![false; x_len * y_len * DIRECTIONS.len()],
        |visited, (x, y)| {
            visited.fill(false);
            tiles[y][x] == Tile::Empty
                && has_loop(visited.as_mut_slice(), tiles.clone(), start, x, y)
        },
    )
    .filter(|&has_loop| has_loop)
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
