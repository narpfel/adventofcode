use std::io;
use std::path::Path;

use graph::ReadExt;
use graph::RectangularWorld;
use graph::World;

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
struct Pipes(RectangularWorld<Point, Tile>);

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
        self.0.get(p)
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
    let pipe_points = pipes.all_reachable_points(start);
    println!("{}", pipe_points.len() / 2);

    enum Direction {
        FromBottom,
        FromTop,
    }
    use Direction::*;

    let mut enclosed_tiles_count = 0;
    for (y, line) in pipes.0.lines().enumerate() {
        let mut crossings = 0;
        let mut on_pipe = None;
        for (x, pipe) in line.iter().enumerate() {
            let x = x as i64;
            let y = y as i64;
            if pipe_points.contains(&(x, y)) {
                match pipe {
                    Vertical => crossings += 1,
                    Horizontal => (),
                    LBend => match on_pipe {
                        Some(_) => unreachable!(),
                        None => on_pipe = Some(FromTop),
                    },
                    JBend => match on_pipe {
                        Some(FromTop) => on_pipe = None,
                        Some(FromBottom) => {
                            crossings += 1;
                            on_pipe = None;
                        }
                        None => unreachable!(),
                    },
                    SevenBend => match on_pipe {
                        Some(FromTop) => {
                            crossings += 1;
                            on_pipe = None;
                        }
                        Some(FromBottom) => {
                            on_pipe = None;
                        }
                        None => unreachable!(),
                    },
                    FBend => match on_pipe {
                        Some(_) => unreachable!(),
                        None => on_pipe = Some(FromBottom),
                    },
                    Ground => (),
                    Start => unreachable!(),
                }
            }
            else if crossings % 2 == 1 {
                enclosed_tiles_count += 1;
            }
        }
    }
    println!("{enclosed_tiles_count}");
}
