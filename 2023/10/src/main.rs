use std::{
    io,
    path::Path,
};

use fnv::FnvHashMap;
use graph::{
    ReadExt,
    World,
};

type Point = (i64, i64);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Tile {
    Vertical,
    Horizontal,
    LBend,
    JBend,
    SevenBend,
    FBend,
    Ground,
    Start,
}

use Tile::*;

impl graph::Tile for Tile {
    fn is_walkable(&self) -> bool {
        !matches!(self, Ground)
    }
}

#[derive(Debug, Clone)]
struct Pipes(FnvHashMap<Point, Tile>);

impl Pipes {
    fn from_file(path: impl AsRef<Path>) -> io::Result<(Self, Point)> {
        let mut pipes = Self(ReadExt::from_file(path)?);
        let start @ (x, y) = pipes.find(&Start).unwrap();
        let connected_to_start = {
            let mut points = [(x - 1, y), (x + 1, y), (x, y - 1), (x, y + 1)]
                .into_iter()
                .filter(|p| pipes.get(p).is_some())
                .filter(|p| pipes.neighbours(*p).any(|p| p == start))
                .collect::<Vec<_>>();
            points.sort_by_key(|(x, y)| (*y, *x));
            points
        };
        let [(x1, y1), (x2, y2)] = &connected_to_start[..]
        else {
            unreachable!()
        };
        let start_tile_type = match ((x1 - x, y1 - y), (x2 - x, y2 - y)) {
            ((0, -1), (0, 1)) => Vertical,
            ((-1, 0), (1, 0)) => Horizontal,
            ((0, -1), (1, 0)) => LBend,
            ((0, -1), (-1, 0)) => JBend,
            ((-1, 0), (0, 1)) => SevenBend,
            ((1, 0), (0, 1)) => FBend,
            _ => unreachable!(),
        };

        pipes.0.insert(start, start_tile_type);

        Ok((pipes, start))
    }
}

impl graph::World for Pipes {
    type Point = Point;
    type Tile = Tile;

    fn get(&self, p: &Self::Point) -> Option<Self::Tile> {
        self.0.get(p).copied()
    }

    fn iter(&self) -> impl Iterator<Item = (Self::Point, &Self::Tile)> {
        World::iter(&self.0)
    }

    fn neighbours(&self, (x, y): Self::Point) -> Box<dyn Iterator<Item = Self::Point>> {
        match self.get(&(x, y)) {
            Some(Vertical) => Box::new([(x, y - 1), (x, y + 1)].into_iter()),
            Some(Horizontal) => Box::new([(x - 1, y), (x + 1, y)].into_iter()),
            Some(LBend) => Box::new([(x, y - 1), (x + 1, y)].into_iter()),
            Some(JBend) => Box::new([(x, y - 1), (x - 1, y)].into_iter()),
            Some(SevenBend) => Box::new([(x - 1, y), (x, y + 1)].into_iter()),
            Some(FBend) => Box::new([(x + 1, y), (x, y + 1)].into_iter()),
            Some(Ground) => Box::new([].into_iter()),
            Some(Start) => unreachable!("has been replaced"),
            None => Box::new([].into_iter()),
        }
    }
}

impl TryFrom<char> for Tile {
    type Error = char;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        Ok(match value {
            '|' => Vertical,
            '-' => Horizontal,
            'L' => LBend,
            'J' => JBend,
            '7' => SevenBend,
            'F' => FBend,
            '.' => Ground,
            'S' => Start,
            c => Err(c)?,
        })
    }
}

fn main() {
    let (pipes, start) = Pipes::from_file("input").unwrap();

    let distance_to_farthest_tile = pipes.walk_cells_breadth_first(&start).last().unwrap().len();
    println!("{}", distance_to_farthest_tile);

    let mut squeeze_through_pipes: FnvHashMap<Point, bool> = pipes
        .all_reachable_points(start)
        .iter()
        .flat_map(|p @ (x, y)| {
            let tile = pipes.get(p).unwrap();
            let x = 2 * x;
            let y = 2 * y;
            let p = (x, y);
            match tile {
                Vertical => [p, (x, y - 1), (x, y + 1)],
                Horizontal => [p, (x - 1, y), (x + 1, y)],
                LBend => [p, (x + 1, y), (x, y - 1)],
                JBend => [p, (x - 1, y), (x, y - 1)],
                SevenBend => [p, (x - 1, y), (x, y + 1)],
                FBend => [p, (x + 1, y), (x, y + 1)],
                Ground => unreachable!("ground is not part of the pipe"),
                Start => unreachable!("has been replaced"),
            }
        })
        .map(|p| (p, false))
        .collect();

    let min_x = pipes.points().map(|(x, _)| x).min().unwrap() * 2;
    let max_x = pipes.points().map(|(x, _)| x).max().unwrap() * 2;
    let min_y = pipes.points().map(|(_, y)| y).min().unwrap() * 2;
    let max_y = pipes.points().map(|(_, y)| y).max().unwrap() * 2;

    for y in min_y - 1..max_y + 2 {
        for x in min_x - 1..max_x + 2 {
            squeeze_through_pipes.entry((x, y)).or_insert(true);
        }
    }

    let outside = squeeze_through_pipes.all_reachable_points((-1, -1));

    let tiles_contained_inside = squeeze_through_pipes
        .iter()
        .filter(|(&(x, y), &not_pipe)| {
            x % 2 == 0 && y % 2 == 0 && not_pipe && !outside.contains(&(x, y))
        })
        .count();
    println!("{tiles_contained_inside}");
}
