#![feature(or_patterns)]

use std::{
    collections::{
        HashMap,
        HashSet,
        VecDeque,
    },
    convert::{
        TryFrom,
        TryInto,
    },
    error::Error,
    io::{
        stdout,
        Write,
    },
};

#[cfg(feature = "interactive")]
use itertools::Itertools;
#[cfg(not(feature = "interactive"))]
use rand::{
    seq::SliceRandom,
    thread_rng,
};
use std::iter::once;

use intcode::{
    Cell,
    Computer,
    IO,
};

type Point = (i64, i64);
type Hull = HashMap<Point, Tile>;

#[derive(Copy, Clone, Debug)]
enum Direction {
    Up,
    Down,
    Right,
    Left,
}
use Direction::*;

impl Direction {
    fn to_cell(&self) -> Cell {
        match self {
            Up => 1,
            Down => 2,
            Right => 3,
            Left => 4,
        }
    }
}

#[cfg(feature = "interactive")]
impl TryFrom<console::Key> for Direction {
    type Error = NotAnArrowKey;

    fn try_from(key: console::Key) -> Result<Direction, NotAnArrowKey> {
        use console::Key::*;
        Ok(match key {
            ArrowUp => Up,
            ArrowDown => Down,
            ArrowRight => Right,
            ArrowLeft => Left,
            _ => Err(NotAnArrowKey)?,
        })
    }
}

#[cfg(feature = "interactive")]
struct NotAnArrowKey;

#[cfg(feature = "interactive")]
fn render(tile: Option<Tile>) -> char {
    match tile {
        Some(Wall) => '\u{2588}',
        Some(Empty) => '.',
        Some(Target) => 'X',
        Some(Myself) => 'o',
        None => ' ',
    }
}

#[derive(PartialEq, Eq, Copy, Clone)]
enum Tile {
    Wall,
    Empty,
    Target,
    Myself,
}
use Tile::*;

impl TryFrom<Cell> for Tile {
    type Error = InvalidTile;

    fn try_from(value: Cell) -> Result<Tile, InvalidTile> {
        Ok(match value {
            0 => Wall,
            1 => Empty,
            2 => Target,
            3 => Myself,
            _ => return Err(InvalidTile(value)),
        })
    }
}

#[derive(Copy, Clone, Debug)]
struct InvalidTile(Cell);

struct State {
    x: i64,
    y: i64,
    last_input: Option<Direction>,
    hull: Hull,
    target: Option<Point>,
    #[cfg(feature = "interactive")]
    term: console::Term,
    #[cfg(not(feature = "interactive"))]
    rng: rand::rngs::ThreadRng,
}

impl State {
    fn new() -> Self {
        let mut hull = Hull::default();
        hull.insert((0, 0), Empty);
        State {
            x: 0,
            y: 0,
            last_input: None,
            hull,
            target: None,
            #[cfg(feature = "interactive")]
            term: console::Term::stdout(),
            #[cfg(not(feature = "interactive"))]
            rng: thread_rng(),
        }
    }
}

impl State {
    #[cfg(feature = "interactive")]
    fn print(&self) {
        let (&min_x, &max_x) = self
            .hull
            .keys()
            .map(|(x, _)| x)
            .minmax()
            .into_option()
            .unwrap();
        let (&min_y, &max_y) = self
            .hull
            .keys()
            .map(|(_, y)| y)
            .minmax()
            .into_option()
            .unwrap();

        print!("\x1B[;H");
        print!(
            "{}",
            (min_y..=max_y)
                .rev()
                .map(|y| (min_x..=max_x)
                    .map(|x| render(self.hull.get(&(x, y)).cloned()))
                    .collect::<String>())
                .join("\n")
        );
        print!("\x1B[{};{}Ho", max_y - self.y + 1, self.x - min_x + 1);
        stdout().flush().unwrap();
    }

    #[cfg(feature = "interactive")]
    fn read_input(&self) -> Option<Direction> {
        self.term.read_key().ok()?.try_into().ok()
    }

    #[cfg(not(feature = "interactive"))]
    fn read_input(&mut self) -> Option<Direction> {
        // TODO: Optimise by systematically exploring the maze instead of performing a
        // random walk.
        [Up, Down, Right, Left].choose(&mut self.rng).copied()
    }

    fn has_unexplored_cells(&self) -> bool {
        self.hull
            .iter()
            .filter_map(|(position, &tile)| {
                if tile == Wall {
                    None
                }
                else {
                    Some(position)
                }
            })
            .flat_map(|&p| neighbours(p))
            .any(|p| !self.hull.contains_key(&p))
    }

    fn solve(&self) -> Option<(u64, u64)> {
        let mut queue = VecDeque::new();
        queue.push_back((self.target?, 0));
        let mut seen = HashSet::new();

        let mut last_distance = None;
        let mut target_distance = None;
        while let Some((point, distance)) = queue.pop_front() {
            last_distance = Some(distance);
            if point == (0, 0) {
                target_distance = Some(distance);
            }
            seen.insert(point);
            queue.extend(neighbours(point).filter_map(|p| {
                self.hull.get(&p).and_then(|&tile| {
                    if tile == Wall || seen.contains(&p) {
                        None
                    }
                    else {
                        Some((p, distance + 1))
                    }
                })
            }));
        }

        target_distance.and_then(|td| last_distance.map(|ld| (td, ld)))
    }
}

impl IO for State {
    fn next_input(&mut self) -> Option<Cell> {
        if !self.has_unexplored_cells() {
            return None;
        }

        self.last_input = self.read_input();
        self.last_input.map(|d| d.to_cell())
    }

    fn output(&mut self, cell: Cell) {
        let state = cell
            .try_into()
            .unwrap_or_else(|val| panic!("Invalid cell value in Tile conversion: {:?}", val));
        match (self.last_input, state) {
            (None, _) => unreachable!(),
            (Some(Up), Empty | Target) => self.y += 1,
            (Some(Down), Empty | Target) => self.y -= 1,
            (Some(Left), Empty | Target) => self.x -= 1,
            (Some(Right), Empty | Target) => self.x += 1,
            _ => {}
        }

        if state == Wall {
            let (x, y) = match self.last_input {
                Some(Up) => (self.x, self.y + 1),
                Some(Down) => (self.x, self.y - 1),
                Some(Left) => (self.x - 1, self.y),
                Some(Right) => (self.x + 1, self.y),
                _ => unreachable!(),
            };
            self.hull.insert((x, y), state);
        }
        else {
            self.hull.insert((self.x, self.y), state);
        }

        if state == Target {
            self.target = Some((self.x, self.y));
        }

        #[cfg(feature = "interactive")]
        self.print();
    }
}

fn neighbours((x, y): (i64, i64)) -> impl Iterator<Item = (i64, i64)> {
    once((x - 1, y))
        .chain(once((x + 1, y)))
        .chain(once((x, y - 1)))
        .chain(once((x, y + 1)))
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut state = State::new();
    let mut computer = Computer::from_file("input", &mut state)?;

    #[cfg(feature = "interactive")]
    print!("\x1B[2J\x1B[?25l\x1B[;Ho");
    stdout().flush()?;
    computer.run();
    #[cfg(feature = "interactive")]
    println!("\x1B[9999;1H\x1B[4F\x1B[?25hGoodbye.");
    if let Some((part1, part2)) = state.solve() {
        println!("{}\n{}", part1, part2);
    }
    else {
        return Err("Failed to find solution".into());
    }
    Ok(())
}
