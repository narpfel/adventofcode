use std::{
    collections::HashMap,
    convert::{
        TryFrom,
        TryInto,
    },
    fs::File,
    hash::Hash,
    io::{
        self,
        BufRead,
        BufReader,
    },
    path::Path,
};

use itertools::Itertools;

use graph::{
    CartesianPoint,
    World,
};

#[derive(Copy, Clone)]
enum Tile {
    Wall,
    Empty,
}

impl TryFrom<char> for Tile {
    type Error = char;

    fn try_from(c: char) -> Result<Self, Self::Error> {
        Ok(match c {
            '#' => Tile::Wall,
            '.' => Tile::Empty,
            _ => return Err(c),
        })
    }
}

impl graph::Tile for Tile {
    fn is_walkable(&self) -> bool {
        match *self {
            Tile::Wall => false,
            Tile::Empty => true,
        }
    }
}

#[derive(Copy, Clone, Debug)]
struct Point {
    point: CartesianPoint,
    additional_neighbour: Option<CartesianPoint>,
}

impl Point {
    fn new(x: usize, y: usize) -> Self {
        Self {
            point: CartesianPoint(x, y),
            additional_neighbour: None,
        }
    }
}

impl graph::Point for Point {
    fn neighbours(&self) -> Vec<Self>
    where
        Self: Sized,
    {
        let mut neighbours = self
            .point
            .neighbours()
            .into_iter()
            .map(|p| Point { point: p, additional_neighbour: None })
            .collect_vec();
        neighbours.extend(
            self.additional_neighbour
                .map(|point| Self { point, additional_neighbour: None })
                .iter(),
        );
        neighbours
    }
}

impl PartialEq for Point {
    fn eq(&self, other: &Self) -> bool {
        self.point == other.point
    }
}

impl Eq for Point {}

impl Hash for Point {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.point.hash(state)
    }
}

#[derive(Clone)]
struct WarpedMaze {
    maze: HashMap<Point, Tile>,
    start_point: Point,
    end_point: Point,
}

impl World for WarpedMaze {
    type Point = Point;
    type Tile = Tile;

    fn get(&self, p: &Self::Point) -> Option<Self::Tile> {
        self.maze.get(p).cloned()
    }

    fn canonicalise_point(&self, p: &Self::Point) -> Self::Point {
        self.maze
            .get_key_value(p)
            .map_or_else(|| unreachable!(), |(p, _)| *p)
    }
}

fn read_input(path: impl AsRef<Path>) -> Result<WarpedMaze, io::Error> {
    let lines = {
        let f = File::open(path)?;
        let reader = BufReader::new(f);
        let mut lines = reader
            .lines()
            .map(|line| line.map(|line| line.chars().collect()))
            .collect::<Result<Vec<Vec<_>>, io::Error>>()?;
        lines.retain(|line| !line.is_empty());
        lines
    };

    let mut maze: HashMap<Point, Tile> = HashMap::default();
    for (y, line) in lines.iter().skip(2).dropping_back(2).enumerate() {
        for (x, &c) in line.iter().skip(2).dropping_back(2).enumerate() {
            if let Ok(tile) = c.try_into() {
                maze.insert(Point::new(x, y), tile);
            }
        }
    }

    let mut warp_points: HashMap<_, Vec<_>> = HashMap::default();
    // This does not work for two adjacent warp points...
    for (y, (l1, l2)) in lines.iter().tuple_windows().enumerate() {
        for (x, (&a, &b)) in l1.iter().zip(l2.iter()).enumerate() {
            if a.is_uppercase() && b.is_uppercase() {
                let y = if y > 0 && lines[y - 1][x] == '.' {
                    y - 1
                }
                else {
                    y + 2
                };
                warp_points.entry((a, b)).or_default().push((x - 2, y - 2));
            }
        }
    }

    for (x1, x2) in (0..lines[0].len()).tuple_windows() {
        for (y, line) in lines.iter().enumerate() {
            let a = line[x1];
            let b = line[x2];
            if a.is_uppercase() && b.is_uppercase() {
                let x = if x1 > 0 && lines[y][x1 - 1] == '.' {
                    x1 - 1
                }
                else {
                    x1 + 2
                };
                warp_points.entry((a, b)).or_default().push((x - 2, y - 2));
            }
        }
    }

    for points in warp_points.values() {
        if points.len() == 2 {
            for (from, to) in points.iter().zip(points.iter().rev()) {
                let (mut k, v) = maze.remove_entry(&Point::new(from.0, from.1)).unwrap();
                k.additional_neighbour = Some(CartesianPoint(to.0, to.1));
                maze.insert(k, v);
            }
        }
    }

    let aa = warp_points[&('A', 'A')][0];
    let start_point = Point::new(aa.0, aa.1);
    let zz = warp_points[&('Z', 'Z')][0];
    let end_point = Point::new(zz.0, zz.1);

    Ok(WarpedMaze { maze, start_point, end_point })
}

fn solve(maze: &WarpedMaze) -> u64 {
    maze.distance(&maze.start_point, &maze.end_point)
        .try_into()
        .unwrap()
}

#[cfg(test)]
mod tests {
    use super::{
        read_input,
        solve,
    };

    #[test]
    fn test_1() {
        assert_eq!(solve(&read_input("input_test_1").unwrap()), 23);
    }

    #[test]
    fn test_2() {
        assert_eq!(solve(&read_input("input_test_2").unwrap()), 58);
    }
}

fn main() {
    println!("{}", solve(&read_input("input").unwrap()));
}
