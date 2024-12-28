use std::cmp::Ordering;
use std::hash::Hash;
use std::io;
use std::path::Path;

use graph::CartesianPoint;
use graph::ReadExt as _;
use graph::World as _;
use rustc_hash::FxHashMap;
use rustc_hash::FxHashSet;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Tile {
    Wall,
    Empty,
    Start,
    End,
}

impl TryFrom<char> for Tile {
    type Error = char;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        Ok(match value {
            'S' => Self::Start,
            'E' => Self::End,
            '#' => Self::Wall,
            '.' => Self::Empty,
            _ => return Err(value),
        })
    }
}

impl graph::Tile for Tile {
    fn is_walkable(&self) -> bool {
        !matches!(self, Self::Wall)
    }
}

impl From<Tile> for char {
    fn from(value: Tile) -> Self {
        match value {
            Tile::Wall => '#',
            Tile::Empty => ' ',
            Tile::Start => 'S',
            Tile::End => 'E',
        }
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Direction {
    #[default]
    Right,
    Down,
    Left,
    Up,
}

impl Direction {
    fn left(self) -> Self {
        match self {
            Direction::Right => Direction::Up,
            Direction::Down => Direction::Right,
            Direction::Left => Direction::Down,
            Direction::Up => Direction::Left,
        }
    }

    fn right(self) -> Self {
        match self {
            Direction::Right => Direction::Down,
            Direction::Down => Direction::Left,
            Direction::Left => Direction::Up,
            Direction::Up => Direction::Right,
        }
    }

    fn vec(self) -> (isize, isize) {
        match self {
            Direction::Right => (1, 0),
            Direction::Down => (0, 1),
            Direction::Left => (-1, 0),
            Direction::Up => (0, -1),
        }
    }

    fn all() -> impl Iterator<Item = Self> {
        [
            Direction::Right,
            Direction::Down,
            Direction::Left,
            Direction::Up,
        ]
        .into_iter()
    }
}

impl std::ops::Add<Direction> for CartesianPoint {
    type Output = Self;

    fn add(self, rhs: Direction) -> Self::Output {
        self + rhs.vec()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct DirectedPoint {
    point: CartesianPoint,
    direction: Direction,
}

impl From<CartesianPoint> for DirectedPoint {
    fn from(point: CartesianPoint) -> Self {
        Self { point, direction: Direction::default() }
    }
}

impl graph::Point for DirectedPoint {
    fn neighbours(self) -> impl Iterator<Item = Self>
    where
        Self: Sized,
    {
        [
            Self {
                point: self.point + self.direction,
                direction: self.direction,
            },
            Self {
                point: self.point + self.direction.left(),
                direction: self.direction.left(),
            },
            Self {
                point: self.point + self.direction.right(),
                direction: self.direction.right(),
            },
        ]
        .into_iter()
    }
}

#[derive(Debug, Clone)]
struct Maze {
    tiles: FxHashMap<CartesianPoint, Tile>,
}

impl graph::World for Maze {
    type Point = DirectedPoint;
    type PointOrder = graph::Unordered;
    type Tile = Tile;

    fn get(&self, p: &Self::Point) -> Option<Self::Tile> {
        self.tiles.get(&p.point).copied()
    }

    fn cost(&self, from: &Self::Point, to: &Self::Point) -> u64 {
        if from.direction != to.direction {
            1001
        }
        else {
            1
        }
    }

    fn iter(&self) -> impl Iterator<Item = (Self::Point, &Self::Tile)> {
        self.tiles
            .iter()
            .map(|(point, tile)| (DirectedPoint::from(*point), tile))
    }
}

fn read_input(path: impl AsRef<Path>) -> io::Result<Maze> {
    Ok(Maze { tiles: FxHashMap::from_file(path)? })
}

fn part_1(maze: &Maze) -> u64 {
    let start = maze.find(&Tile::Start).unwrap();
    let end = maze.find(&Tile::End).unwrap();
    maze.distance_with(&start, |p| p.point == end.point)
        .try_into()
        .unwrap()
}

fn part_2(maze: &Maze, max_cost: u64) -> usize {
    let start = maze.find(&Tile::Start).unwrap();
    let end = maze.find(&Tile::End).unwrap();
    let mut points = FxHashMap::default();
    points.insert(start, (max_cost, vec![start]));

    let mut next_points = graph::MonotonicPriorityQueue::<graph::Unordered, _>::default();
    next_points.push(0, (start, start));

    while let Some((cost, (p, prev))) = next_points.pop() {
        if cost > max_cost {
            break;
        }

        let (known_minimal_cost, points_in_path) =
            points.entry(p).or_insert_with(|| (max_cost, vec![]));
        match cost.cmp(known_minimal_cost) {
            Ordering::Less => {
                *known_minimal_cost = cost;
                *points_in_path = vec![prev];
                for new_p in maze.neighbours(p) {
                    next_points.push(cost + maze.cost(&p, &new_p), (new_p, p));
                }
            }
            Ordering::Equal => {
                points_in_path.push(prev);
            }
            Ordering::Greater => (),
        }
    }

    let mut points_on_any_best_path = FxHashSet::default();
    let mut todo = Direction::all()
        .map(|d| DirectedPoint { point: end.point, direction: d })
        .collect::<Vec<_>>();
    while let Some(p) = todo.pop() {
        points_on_any_best_path.insert(p);
        for &p in points
            .get(&p)
            .map(|(_, prevs)| prevs)
            .unwrap_or(const { &Vec::new() })
        {
            if !points_on_any_best_path.contains(&p) {
                todo.push(p);
            }
        }
    }
    points_on_any_best_path
        .iter()
        .map(|p| p.point)
        .collect::<FxHashSet<_>>()
        .len()
}

#[test]
fn test_part_1() -> io::Result<()> {
    assert_eq!(part_1(&read_input("input_test")?), 11048);
    assert_eq!(part_1(&read_input("input_test_2")?), 7036);
    Ok(())
}

#[test]
fn test_part_2() -> io::Result<()> {
    let maze = read_input("input_test")?;
    assert_eq!(part_2(&maze, part_1(&maze)), 64);
    let maze = read_input("input_test_2")?;
    assert_eq!(part_2(&maze, part_1(&maze)), 45);
    Ok(())
}

fn main() -> io::Result<()> {
    let maze = read_input("input")?;
    let best_path_cost = part_1(&maze);
    println!("{}", best_path_cost);
    println!("{}", part_2(&maze, best_path_cost));
    Ok(())
}
