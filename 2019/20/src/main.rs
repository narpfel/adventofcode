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
    Point,
    World,
};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
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
struct WarpedPoint {
    inner: CartesianPoint,
    additional_neighbour: Option<CartesianPoint>,
}

impl WarpedPoint {
    fn new(x: usize, y: usize) -> Self {
        Self {
            inner: CartesianPoint(x, y),
            additional_neighbour: None,
        }
    }
}

impl graph::Point for WarpedPoint {
    fn neighbours(&self) -> Vec<Self>
    where
        Self: Sized,
    {
        let mut neighbours = self
            .inner
            .neighbours()
            .into_iter()
            .map(|p| WarpedPoint { inner: p, additional_neighbour: None })
            .collect_vec();
        neighbours.extend(
            self.additional_neighbour
                .map(|point| Self { inner: point, additional_neighbour: None })
                .iter(),
        );
        neighbours
    }
}

impl PartialEq for WarpedPoint {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl Eq for WarpedPoint {}

impl Hash for WarpedPoint {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.inner.hash(state)
    }
}

#[derive(Clone)]
struct WarpedMaze {
    inner: HashMap<WarpedPoint, Tile>,
    start_point: WarpedPoint,
    end_point: WarpedPoint,
}

impl World for WarpedMaze {
    type Point = WarpedPoint;
    type Tile = Tile;

    fn get(&self, p: &Self::Point) -> Option<Self::Tile> {
        self.inner.get(p).cloned()
    }

    fn canonicalise_point(&self, p: &Self::Point) -> Self::Point {
        self.inner
            .get_key_value(p)
            .map_or_else(|| unreachable!(), |(p, _)| *p)
    }

    fn find(&self, tile: &Self::Tile) -> Option<Self::Point> {
        self.inner.find(tile)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct FractalPoint {
    inner: WarpedPoint,
    level: u64,
}

impl Point for FractalPoint {
    fn neighbours(&self) -> Vec<Self>
    where
        Self: Sized,
    {
        unimplemented!("we don’t need this")
    }
}

#[derive(Clone)]
struct FractalMaze {
    inner: WarpedMaze,
    size: CartesianPoint,
}

impl FractalMaze {
    fn new(maze: WarpedMaze) -> Self {
        let size = maze.inner.keys().map(|p| p.inner).max().unwrap();
        Self { inner: maze, size }
    }

    fn is_outer(&self, point: <FractalMaze as World>::Point) -> bool {
        let CartesianPoint(x, y) = point.inner.inner;
        x == 0 || y == 0 || x == self.size.0 || y == self.size.1
    }
}

impl World for FractalMaze {
    type Point = FractalPoint;
    type Tile = <WarpedMaze as World>::Tile;

    fn get(&self, p: &Self::Point) -> Option<Self::Tile> {
        self.inner.get(&p.inner)
    }

    fn canonicalise_point(&self, point: &Self::Point) -> Self::Point {
        FractalPoint {
            inner: self.inner.canonicalise_point(&point.inner),
            ..*point
        }
    }

    fn neighbours<'a>(&'a self, point: Self::Point) -> Box<dyn Iterator<Item = Self::Point> + 'a> {
        Box::new(Neighbours {
            maze: self,
            point,
            points: self.inner.neighbours(point.inner),
        })
    }

    fn find(&self, tile: &Self::Tile) -> Option<Self::Point> {
        self.inner
            .find(tile)
            .map(|inner| FractalPoint { inner, level: 0 })
    }
}

struct Neighbours<'a> {
    maze: &'a FractalMaze,
    point: <FractalMaze as World>::Point,
    points: Box<dyn Iterator<Item = <WarpedMaze as World>::Point> + 'a>,
}

impl<'a> Iterator for Neighbours<'a> {
    type Item = <FractalMaze as World>::Point;

    fn next(&mut self) -> Option<Self::Item> {
        let level = self.point.level;
        self.points.next().and_then(|point| {
            let is_end_point_but_wrong_level = point == self.maze.inner.end_point && level != 0;
            let would_go_outside_on_outermost_level = level == 0
                && self.maze.is_outer(self.point)
                && !self.point.inner.inner.is_direct_neighbour(point.inner);
            if is_end_point_but_wrong_level || would_go_outside_on_outermost_level {
                None
            }
            else if self.point.inner.inner.is_direct_neighbour(point.inner) {
                Some(FractalPoint { inner: point, level })
            }
            else if self.maze.is_outer(FractalPoint { inner: point, level: 0 }) {
                Some(FractalPoint { inner: point, level: level + 1 })
            }
            else {
                Some(FractalPoint { inner: point, level: level - 1 })
            }
        })
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

    let mut maze = HashMap::default();
    for (y, line) in lines.iter().skip(2).dropping_back(2).enumerate() {
        for (x, &c) in line.iter().skip(2).dropping_back(2).enumerate() {
            if let Ok(tile) = c.try_into() {
                maze.insert(WarpedPoint::new(x, y), tile);
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
                let (mut k, v) = maze
                    .remove_entry(&WarpedPoint::new(from.0, from.1))
                    .unwrap();
                k.additional_neighbour = Some(CartesianPoint(to.0, to.1));
                maze.insert(k, v);
            }
        }
    }

    let aa = warp_points[&('A', 'A')][0];
    let start_point = WarpedPoint::new(aa.0, aa.1);
    let zz = warp_points[&('Z', 'Z')][0];
    let end_point = WarpedPoint::new(zz.0, zz.1);

    Ok(WarpedMaze { inner: maze, start_point, end_point })
}

fn solve_part_1(maze: &WarpedMaze) -> u64 {
    maze.distance(&maze.start_point, &maze.end_point)
        .try_into()
        .unwrap()
}

fn solve_part_2(maze: &FractalMaze) -> u64 {
    maze.distance(
        &FractalPoint { inner: maze.inner.start_point, level: 0 },
        &FractalPoint { inner: maze.inner.end_point, level: 0 },
    )
    .try_into()
    .unwrap()
}

#[cfg(test)]
mod tests {
    use graph::World;

    use super::{
        read_input,
        solve_part_1,
        solve_part_2,
        FractalMaze,
        FractalPoint,
        WarpedPoint,
    };

    #[test]
    fn test_1() {
        assert_eq!(solve_part_1(&read_input("input_test_1").unwrap()), 23);
    }

    #[test]
    fn test_2() {
        assert_eq!(solve_part_1(&read_input("input_test_2").unwrap()), 58);
    }

    #[test]
    fn test_neighbours() {
        let maze = FractalMaze::new(read_input("input_test_part_2").unwrap());
        let xf = maze.canonicalise_point(&FractalPoint {
            inner: WarpedPoint::new(15, 26),
            level: 0,
        });
        let neighbours = maze.neighbours(xf);
        assert_eq!(neighbours.count(), 2);
        assert!(maze.is_outer(FractalPoint { inner: WarpedPoint::new(0, 27), level: 0 }));
        assert!(maze.is_outer(FractalPoint {
            inner: WarpedPoint::new(40, 11),
            level: 0
        }));
        assert!(maze.is_outer(FractalPoint {
            inner: WarpedPoint::new(13, 32),
            level: 0
        }));
        assert!(maze.is_outer(FractalPoint { inner: WarpedPoint::new(17, 0), level: 0 }));
    }

    #[test]
    fn test_part_2() {
        let maze = FractalMaze::new(read_input("input_test_part_2").unwrap());
        assert_eq!(solve_part_2(&maze), 396);
    }
}

fn main() {
    let maze = read_input("input").unwrap();
    println!("{}", solve_part_1(&maze));
    println!("{}", solve_part_2(&FractalMaze::new(maze)));
}
