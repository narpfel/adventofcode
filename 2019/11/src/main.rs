use std::collections::HashMap;
use std::error::Error;

use intcode::Cell;
use intcode::Computer;
use intcode::IO;

#[derive(Debug, Copy, Clone)]
enum Direction {
    Up,
    Down,
    Left,
    Right,
}
use Direction::*;

#[derive(Debug, Copy, Clone)]
enum Colour {
    Black,
    White,
}
use Colour::*;

fn next_direction(direction: Direction, turn: i64) -> Option<Direction> {
    match (direction, turn) {
        (Up, 0) => Some(Left),
        (Up, 1) => Some(Right),
        (Down, 0) => Some(Right),
        (Down, 1) => Some(Left),
        (Left, 0) => Some(Down),
        (Left, 1) => Some(Up),
        (Right, 0) => Some(Up),
        (Right, 1) => Some(Down),
        _ => None,
    }
}

fn move_((mut x, mut y): (i64, i64), direction: Direction) -> (i64, i64) {
    match direction {
        Up => y += 1,
        Down => y -= 1,
        Left => x -= 1,
        Right => x += 1,
    };
    (x, y)
}

struct State<'a> {
    tiles: &'a mut HashMap<(i64, i64), Colour>,
    position: (i64, i64),
    direction: Direction,
    colour: Option<Cell>,
}

impl<'a> State<'a> {
    fn new(tiles: &mut HashMap<(i64, i64), Colour>) -> State {
        State {
            tiles,
            position: (0, 0),
            direction: Direction::Up,
            colour: None,
        }
    }
}

impl<'a> IO for State<'a> {
    fn next_input(&mut self) -> Option<Cell> {
        Some(
            self.tiles
                .get(&self.position)
                .map(|colour| match colour {
                    Black => 0,
                    White => 1,
                })
                .unwrap_or(0),
        )
    }

    fn output(&mut self, value: Cell) {
        if let Some(colour) = self.colour.take() {
            self.tiles.insert(
                self.position,
                match colour {
                    0 => Black,
                    1 => White,
                    _ => panic!(),
                },
            );
            self.direction = next_direction(self.direction, value).unwrap();
            self.position = move_(self.position, self.direction);
        }
        else {
            self.colour = Some(value);
        }
    }
}

fn solve(tiles: &mut HashMap<(i64, i64), Colour>) -> Result<(), Box<dyn Error>> {
    let mut state = State::new(tiles);
    let mut c = Computer::from_file("input", &mut state)?;
    c.run().ok_or("error while executing program")?;
    Ok(())
}

fn part1() -> Result<usize, Box<dyn Error>> {
    let mut tiles = HashMap::new();
    solve(&mut tiles)?;
    Ok(tiles.len())
}

fn part2() -> Result<String, Box<dyn Error>> {
    let mut tiles = HashMap::new();
    tiles.insert((0, 0), White);
    solve(&mut tiles)?;

    let (min_x, min_y) = tiles.keys().fold((1, 0), |(min_x, min_y), (x, y)| {
        (*x.min(&min_x), *y.min(&min_y))
    });
    let mut lines: Vec<Vec<char>> = Vec::new();
    for ((x, y), ref colour) in tiles {
        if y - min_y >= lines.len() as i64 {
            lines.resize((y - min_y + 1).try_into()?, Vec::new());
        }
        let line = &mut lines[(y - min_y) as usize];
        if x - min_x >= line.len() as i64 {
            line.resize((x - min_x + 1).try_into()?, ' ');
        }
        line[(x - min_x) as usize] = match colour {
            White => '#',
            Black => ' ',
        };
    }
    Ok(lines
        .iter()
        .rev()
        .map(|line| line.iter().collect())
        .collect::<Vec<String>>()
        .join("\n"))
}

fn main() -> Result<(), Box<dyn Error>> {
    println!("{}", part1()?);
    println!("{}", part2()?);
    Ok(())
}
