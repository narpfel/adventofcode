use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};
use std::error::Error;
use std::iter::once;

use intcode::{Cell, Computer, IO};

type Scaffolding = HashMap<Point, Tile>;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct Point {
    x: i64,
    y: i64,
}

#[derive(Debug, PartialEq)]
enum Tile {
    Scaffold,
    Empty,
    Up,
    Down,
    Left,
    Right,
}
use Tile::*;

#[derive(Debug)]
struct InvalidTile;

impl TryFrom<Cell> for Tile {
    type Error = InvalidTile;

    fn try_from(cell: Cell) -> Result<Self, Self::Error> {
        Ok(match u8::try_from(cell).map_err(|_| InvalidTile)? as char {
            '#' => Scaffold,
            '.' => Empty,
            '^' => Up,
            'v' => Down,
            '<' => Left,
            '>' => Right,
            _ => return Err(InvalidTile),
        })
    }
}

struct State {
    position: Point,
    scaffolding: Scaffolding,
}

impl State {
    fn new() -> Self {
        State {
            position: Point { x: 0, y: 0 },
            scaffolding: Scaffolding::default(),
        }
    }

    fn intersections<'a>(&'a self) -> impl Iterator<Item = Point> + 'a {
        self.scaffolding
            .keys()
            .filter(move |&&p| {
                neighbours(p).chain(once(p)).all(|n| {
                    self.scaffolding
                        .get(&n)
                        .map(|tile| tile == &Scaffold)
                        .unwrap_or(false)
                })
            })
            .copied()
    }

    fn part1(&self) -> Cell {
        self.intersections().map(|Point { x, y }| x * y).sum()
    }
}

impl IO for State {
    fn next_input(&mut self) -> Option<Cell> {
        None
    }

    fn output(&mut self, cell: Cell) {
        #[cfg(feature = "interactive")]
        print!("{}", cell as u8 as char);
        if is_newline(cell) {
            self.position = Point {
                x: 0,
                y: self.position.y + 1,
            };
        } else if let Ok(tile) = cell.try_into() {
            self.scaffolding.insert(self.position, tile);
            self.position = Point {
                x: self.position.x + 1,
                ..self.position
            };
        }
    }
}

fn is_newline(cell: Cell) -> bool {
    cell == 10
}

fn neighbours(Point { x, y }: Point) -> impl Iterator<Item = Point> {
    once(Point { x: x - 1, y })
        .chain(once(Point { x: x + 1, y }))
        .chain(once(Point { x, y: y - 1 }))
        .chain(once(Point { x, y: y + 1 }))
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut state = State::new();
    let mut computer = Computer::from_file("input", &mut state)?;

    computer.run();
    println!("{}", state.part1());

    Ok(())
}
