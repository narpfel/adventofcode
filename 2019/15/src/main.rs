use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::error::Error;
use std::io::stdout;
use std::io::Write;
#[cfg(not(feature = "interactive"))]
use std::iter::repeat;

use graph::Point as _;
use graph::World;
use intcode::Cell;
use intcode::Computer;
use intcode::IO;
use itertools::Itertools;

type Point = (i64, i64);

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Direction {
    Up,
    Down,
    Right,
    Left,
}
use Direction::*;

impl Direction {
    fn to_cell(self) -> Cell {
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
            _ => return Err(NotAnArrowKey),
        })
    }
}

#[cfg(feature = "interactive")]
struct NotAnArrowKey;

fn render(tile: Option<Tile>) -> char {
    match tile {
        Some(Wall) => '\u{2588}',
        Some(Empty) => '.',
        Some(Target) => 'X',
        Some(Unknown) => ' ',
        None => ' ',
    }
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
enum Tile {
    Wall,
    Empty,
    Target,
    Unknown,
}
use Tile::*;

impl Tile {
    fn is_known(self) -> bool {
        !matches!(self, Unknown)
    }
}

impl graph::Tile for Tile {
    fn is_walkable(&self) -> bool {
        !matches!(self, Wall)
    }
}

impl TryFrom<Cell> for Tile {
    type Error = InvalidTile;

    fn try_from(value: Cell) -> Result<Tile, InvalidTile> {
        Ok(match value {
            0 => Wall,
            1 => Empty,
            2 => Target,
            _ => return Err(InvalidTile(value)),
        })
    }
}

#[derive(Copy, Clone, Debug)]
struct InvalidTile(#[expect(dead_code)] Cell);

#[derive(Clone, Debug, Default)]
struct Hull {
    map: HashMap<Point, Tile>,
}

impl Hull {
    fn insert(&mut self, key: Point, value: Tile) -> Option<Tile> {
        self.map.insert(key, value)
    }

    fn keys(&self) -> impl Iterator<Item = &Point> {
        self.map.keys()
    }
}

impl graph::World for Hull {
    type Point = Point;
    type Tile = Tile;

    fn get(&self, p: &Self::Point) -> Option<Self::Tile> {
        Some(self.map.get(p).cloned().unwrap_or(Unknown))
    }

    fn iter(&self) -> impl Iterator<Item = (Self::Point, &Self::Tile)> {
        unimplemented!();
        #[expect(unreachable_code)]
        [].into_iter()
    }
}

#[derive(Debug)]
struct State {
    x: i64,
    y: i64,
    last_input: Option<Direction>,
    hull: Hull,
    target: Option<Point>,
    #[cfg(feature = "interactive")]
    term: console::Term,
    path: VecDeque<Direction>,
    visualise: bool,
}

impl State {
    fn new(visualise: bool) -> Self {
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
            path: VecDeque::default(),
            visualise,
        }
    }
}

impl State {
    fn print(&self) {
        let ((min_x, min_y), (max_x, max_y)) = self.dimensions();

        print!("\x1B[;H");
        print!(
            "{}",
            (min_y..=max_y)
                .rev()
                .map(|y| (min_x..=max_x)
                    .map(|x| render(self.hull.get(&(x, y))))
                    .collect::<String>())
                .join("\n")
        );
        print!(
            "\x1B[s\x1B[{};{}Ho\x1B[u",
            max_y - self.y + 1,
            self.x - min_x + 1
        );

        stdout().flush().unwrap();
    }

    fn dimensions(&self) -> (Point, Point) {
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
        ((min_x, min_y), (max_x, max_y))
    }

    #[cfg(feature = "interactive")]
    fn read_input(&self) -> Option<Direction> {
        self.term.read_key().ok()?.try_into().ok()
    }

    #[cfg(not(feature = "interactive"))]
    fn read_input(&mut self) -> Option<Direction> {
        if self.path.is_empty() {
            self.path = self
                .hull
                .path(&(self.x, self.y), &self.next_unexplored_cell()?)?
                .into_iter()
                .tuple_windows()
                .map(|(from, to)| direction(from, to))
                .collect();
        }
        self.path.pop_front()
    }

    fn solve(&self) -> Option<(u64, u64)> {
        Some((
            self.hull.distance(&self.target?, &(0, 0)).try_into().ok()?,
            self.hull
                .walk_cells_breadth_first(&self.target?)
                .last()?
                .len() as _,
        ))
    }

    #[cfg(not(feature = "interactive"))]
    fn next_unexplored_cell(&self) -> Option<Point> {
        // BFS around current position

        let neighbours_with_tile =
            |point: Point| point.neighbours().zip(repeat(self.hull.get(&point)));

        let mut queue: VecDeque<_> = neighbours_with_tile((self.x, self.y)).collect();
        let mut seen = HashSet::new();
        seen.insert((self.x, self.y));

        while let Some((point, neighbour_tile)) = queue.pop_front() {
            let tile = self.hull.get(&point);
            if neighbour_tile.map(|tile| tile == Empty).unwrap_or(false)
                && !tile.is_some_and(Tile::is_known)
            {
                return Some(point);
            }
            seen.insert(point);
            if tile == Some(Empty) {
                queue.extend(neighbours_with_tile(point).filter(|(p, _)| !seen.contains(p)));
            }
        }

        None
    }
}

impl IO for State {
    fn next_input(&mut self) -> Option<Cell> {
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

        if self.visualise {
            self.print();
            #[cfg(not(feature = "interactive"))]
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
    }
}

fn direction((x, y): Point, (a, b): Point) -> Direction {
    if x - a == 1 {
        Left
    }
    else if x - a == -1 {
        Right
    }
    else if y - b == 1 {
        Down
    }
    else if y - b == -1 {
        Up
    }
    else {
        unreachable!()
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    #[cfg(feature = "interactive")]
    let interactive = true;
    #[cfg(not(feature = "interactive"))]
    let interactive = false;

    let visualise = interactive || std::env::args().nth(1) == Some("--visualise".to_owned());

    let mut state = State::new(visualise);
    let mut computer = Computer::from_file("input", &mut state)?;

    if visualise {
        print!("\x1B[2J\x1B[?25l\x1B[;Ho");
        stdout().flush()?;
    }
    computer.run();
    if visualise {
        println!("\x1B[?25h\nGoodbye.");
    }

    if let Some((part1, part2)) = state.solve() {
        println!("{}\n{}", part1, part2);
    }
    else {
        return Err("Failed to find solution".into());
    }
    Ok(())
}
