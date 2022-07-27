use std::{
    error::Error,
    fs::File,
    io::{
        self,
        BufRead,
        BufReader,
    },
    path::Path,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Tile {
    RightCucumber,
    DownCucumber,
    Empty,
}

#[derive(Debug, Clone, Copy)]
struct Invalid(char);

impl Tile {
    fn next_pos(self, tiles: &[Vec<Tile>], x: usize, y: usize) -> (usize, usize) {
        match self {
            Tile::RightCucumber => ((x + 1) % tiles[y].len(), y),
            Tile::DownCucumber => (x, (y + 1) % tiles.len()),
            Tile::Empty => unreachable!(),
        }
    }

    fn is_empty(self) -> bool {
        matches!(self, Tile::Empty)
    }
}

impl TryFrom<char> for Tile {
    type Error = Invalid;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        Ok(match value {
            '>' => Tile::RightCucumber,
            'v' => Tile::DownCucumber,
            '.' => Tile::Empty,
            _ => return Err(Invalid(value)),
        })
    }
}

fn solve(path: impl AsRef<Path>) -> Result<u64, Box<dyn Error>> {
    let input_file = File::open(path.as_ref())?;
    let reader = BufReader::new(input_file);
    let lines = reader.lines().collect::<Result<Vec<_>, io::Error>>()?;
    let mut tiles = lines
        .into_iter()
        .map(|line| {
            line.chars()
                .map(Tile::try_from)
                .collect::<Result<Vec<_>, _>>()
                .unwrap()
        })
        .collect::<Vec<_>>();

    let mut can_move = tiles
        .iter()
        .map(|line| line.iter().map(|_| false).collect())
        .collect::<Vec<Vec<_>>>();

    let mut iteration_count = 0;
    loop {
        iteration_count += 1;
        let mut any_moved = false;
        for current_type in [Tile::RightCucumber, Tile::DownCucumber] {
            for y in 0..tiles.len() {
                for x in 0..tiles[y].len() {
                    let tile = tiles[y][x];
                    if tile == current_type {
                        let next_pos = tile.next_pos(&tiles, x, y);
                        if tiles[next_pos.1][next_pos.0].is_empty() {
                            can_move[y][x] = true;
                            any_moved = true;
                        }
                    }
                }
            }
            for y in 0..tiles.len() {
                for x in 0..tiles[y].len() {
                    if can_move[y][x] {
                        let tile = tiles[y][x];
                        let next_pos = tile.next_pos(&tiles, x, y);
                        tiles[y][x] = Tile::Empty;
                        tiles[next_pos.1][next_pos.0] = tile;
                    }
                }
            }
            can_move.iter_mut().for_each(|line| line.fill(false));
        }
        if !any_moved {
            return Ok(iteration_count);
        }
    }
}

#[cfg(test)]
#[test]
fn test() {
    assert_eq!(solve("input_test").unwrap(), 58);
}

fn main() -> Result<(), Box<dyn Error>> {
    println!("{}", solve("input")?);
    Ok(())
}
