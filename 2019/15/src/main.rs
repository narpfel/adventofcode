#![feature(or_patterns)]

use std::{
    cmp::Reverse,
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

#[cfg(not(feature = "interactive"))]
use std::iter::repeat;

use itertools::Itertools;
use std::iter::once;

use intcode::{
    Cell,
    Computer,
    IO,
};

type Point = (i64, i64);
type Hull = HashMap<Point, Tile>;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
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
        None => ' ',
    }
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
enum Tile {
    Wall,
    Empty,
    Target,
}
use Tile::*;

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
struct InvalidTile(Cell);

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
                    .map(|x| render(self.hull.get(&(x, y)).cloned()))
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
                .find_path((self.x, self.y), self.next_unexplored_cell()?)
                .iter()
                .copied()
                .collect();
        }
        self.path.pop_front()
    }

    /// Dijkstra’s algorithm
    fn find_path(&self, start: Point, end: Point) -> Vec<Direction> {
        #[derive(Default, Debug, PartialOrd, Ord, PartialEq, Eq, Copy, Clone)]
        struct Distance(Reverse<Option<Reverse<u64>>>);

        impl Distance {
            fn new(distance: u64) -> Distance {
                Distance(Reverse(Some(Reverse(distance))))
            }

            fn infinity() -> Distance {
                Self::default()
            }

            fn map(self, f: impl FnOnce(u64) -> u64) -> Self {
                Distance(Reverse(self.0 .0.map(|Reverse(d)| Reverse(f(d)))))
            }
        }

        let (bottom_left, top_right) = self.dimensions();
        let size = (
            top_right.0 - bottom_left.0 + 3,
            top_right.1 - bottom_left.1 + 3,
        );

        let index = |(x, y)| ((y - bottom_left.1 + 1) * size.0 + x - bottom_left.0 + 1) as usize;
        let reverse_index = |i| {
            (
                i as i64 % size.0 + bottom_left.0 - 1,
                i as i64 / size.0 + bottom_left.1 - 1,
            )
        };

        let mut distances: Vec<_> = (bottom_left.1 - 1..=top_right.1 + 1)
            .flat_map(|y| {
                (bottom_left.0 - 1..=top_right.0 + 1).map(move |x| {
                    if (x, y) == start {
                        Distance::new(0)
                    }
                    else {
                        Distance::infinity()
                    }
                })
            })
            .collect();

        let mut unvisited: Vec<_> = distances.iter().map(|_| true).collect();

        let mut previous_point: Vec<_> = distances.iter().map(|_| None).collect();

        while let Some(((current_index, _), _)) = unvisited
            .iter()
            .enumerate()
            .zip(distances.iter())
            .filter(|&((_, &unvisited), _)| unvisited)
            .min_by_key(|(_, &distance)| distance)
        {
            let current = reverse_index(current_index);
            unvisited[current_index] = false;

            for neighbour in neighbours(&reverse_index(current_index))
                .filter(|&p| *unvisited.get(index(p)).unwrap_or(&false))
            {
                let distance = if self.hull.get(&neighbour) == Some(&Wall) {
                    Distance::infinity()
                }
                else {
                    distances[current_index].map(|d| d + 1)
                };
                distances[index(neighbour)] = std::cmp::min(distances[index(neighbour)], distance);
                previous_point[index(neighbour)] = Some(current_index);
            }

            if current == end {
                let mut path = vec![current];

                let mut current_index = current_index;
                while let Some(&Some(index)) = previous_point.get(current_index) {
                    path.push(reverse_index(index));
                    current_index = index;
                }
                return path
                    .into_iter()
                    .rev()
                    .tuple_windows()
                    .map(|(from, to)| direction(from, to))
                    .collect();
            }
        }

        unreachable!();
    }

    fn floodfill(&self, start: Point) -> Option<u64> {
        let mut queue = VecDeque::new();
        queue.push_back((start, 0));
        let mut seen = HashSet::new();

        let mut last_distance = None;
        while let Some((point, distance)) = queue.pop_front() {
            last_distance = Some(distance);
            seen.insert(point);
            queue.extend(neighbours(&point).filter_map(|p| {
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
        last_distance
    }

    fn solve(&self) -> Option<(u64, u64)> {
        Some((
            self.find_path(self.target?, (0, 0)).len() as _,
            self.floodfill(self.target?)?,
        ))
    }

    #[cfg(not(feature = "interactive"))]
    fn next_unexplored_cell(&self) -> Option<Point> {
        // BFS around current position

        let neighbours_with_tile = |ref point| neighbours(point).zip(repeat(self.hull.get(point)));

        let mut queue: VecDeque<_> = neighbours_with_tile((self.x, self.y)).collect();
        let mut seen = HashSet::new();
        seen.insert((self.x, self.y));

        while let Some((point, neighbour_tile)) = queue.pop_front() {
            let tile = self.hull.get(&point);
            if neighbour_tile.map(|&tile| tile == Empty).unwrap_or(false) && tile.is_none() {
                return Some(point);
            }
            seen.insert(point);
            if tile == Some(&Empty) {
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

fn neighbours(&(x, y): &Point) -> impl Iterator<Item = Point> {
    once((x - 1, y))
        .chain(once((x + 1, y)))
        .chain(once((x, y - 1)))
        .chain(once((x, y + 1)))
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
