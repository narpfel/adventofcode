use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::iter::from_fn;
use std::path::Path;

use fnv::FnvHashMap;
use fnv::FnvHashSet;
use graph::CartesianPoint;
use graph::Distance;
use graph::ReadExt as _;
use graph::RectangularWorld;
use graph::World;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Tile {
    Path,
    Forest,
    Left,
    Right,
    Up,
    Down,
}

use Tile::*;

impl TryFrom<char> for Tile {
    type Error = char;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        match value {
            '.' => Ok(Path),
            '#' => Ok(Tile::Forest),
            '>' => Ok(Left),
            '<' => Ok(Right),
            'v' => Ok(Down),
            '^' => Ok(Up),
            _ => Err(value),
        }
    }
}

impl graph::Tile for Tile {
    fn is_walkable(&self) -> bool {
        !matches!(self, Tile::Forest)
    }
}

#[derive(Debug, Clone)]
struct Forest<S: Slipperiness>(RectangularWorld<CartesianPoint, Tile>, S);

impl<S: Slipperiness> Forest<S> {
    fn distances_with<'a>(
        &'a self,
        start: CartesianPoint,
        mut is_at_end: impl FnMut(CartesianPoint) -> bool + 'a,
    ) -> impl Iterator<Item = (CartesianPoint, Distance)> + 'a {
        let mut distance_prev = FnvHashMap::default();
        distance_prev.insert(self.canonicalise_point(&start), (Distance::new(0), None));
        let mut next_points = BinaryHeap::new();
        next_points.push(Reverse((Distance::new(0), self.canonicalise_point(&start))));

        from_fn(move || {
            while let Some(Reverse((distance, point))) = next_points.pop() {
                if point != start && is_at_end(point) {
                    return Some((point, distance));
                }
                else {
                    for neighbour in self.neighbours(point).map(|p| self.canonicalise_point(&p)) {
                        let distance = if !self.is_walkable(&neighbour) {
                            Distance::infinity()
                        }
                        else {
                            distance.map(|d| d + self.cost(&point, &neighbour))
                        };
                        if distance_prev
                            .get(&neighbour)
                            .is_none_or(|(d, _)| d > &distance)
                        {
                            distance_prev.insert(neighbour, (distance, Some(point)));
                            next_points.push(Reverse((distance, neighbour)));
                        }
                    }
                }
            }

            None
        })
    }
}

impl<S: Slipperiness> World for Forest<S> {
    type Point = CartesianPoint;
    type Tile = Tile;

    fn get(&self, p: &Self::Point) -> Option<Self::Tile> {
        self.0.get(p)
    }

    fn iter(&self) -> impl Iterator<Item = (Self::Point, &Self::Tile)> {
        self.0.iter()
    }

    fn neighbours(&self, point: Self::Point) -> impl Iterator<Item = Self::Point> {
        self.1.neighbours(self, point)
    }
}

trait Slipperiness: Clone + Copy {
    fn neighbours(
        self,
        forest: &Forest<Self>,
        point: <Forest<Self> as World>::Point,
    ) -> impl Iterator<Item = <Forest<Self> as World>::Point>;
}

#[derive(Debug, Clone, Copy)]
struct Slippery;

impl Slipperiness for Slippery {
    fn neighbours(
        self,
        forest: &Forest<Self>,
        point: <Forest<Slippery> as World>::Point,
    ) -> impl Iterator<Item = <Forest<Slippery> as World>::Point> {
        let ty = forest.get(&point).unwrap();
        let CartesianPoint(x, y) = point;
        forest
            .0
            .neighbours(point)
            .filter(move |&CartesianPoint(x2, y2)| match ty {
                Tile::Path => true,
                Tile::Forest => false,
                Left => x2 == x + 1 && y == y2,
                Right => x2 == x - 1 && y == y2,
                Up => x == x2 && y2 == y - 1,
                Down => x == x2 && y2 == y + 1,
            })
    }
}

#[derive(Debug, Clone, Copy)]
struct NotSlippery;

impl Slipperiness for NotSlippery {
    fn neighbours(
        self,
        forest: &Forest<Self>,
        point: <Forest<Self> as World>::Point,
    ) -> impl Iterator<Item = <Forest<Self> as World>::Point> {
        forest.0.neighbours(point)
    }
}

struct Graph {
    points: FnvHashMap<CartesianPoint, usize>,
    adjacency: Vec<Vec<Option<u64>>>,
    neighbours: Vec<Vec<usize>>,
}

impl Graph {
    fn from_map(map: FnvHashMap<(CartesianPoint, CartesianPoint), u64>) -> Self {
        let mut points = map
            .keys()
            .flat_map(|&(start, end)| [start, end])
            .collect::<FnvHashSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        points.sort_by_key(|&CartesianPoint(x, y)| (y, x));

        assert!(points.len() < 64);

        let points = points
            .into_iter()
            .enumerate()
            .map(|(i, p)| (p, i))
            .collect::<FnvHashMap<_, _>>();

        let mut adjacency = vec![vec![None; points.len()]; points.len()];
        for (&(start, end), &distance) in &map {
            adjacency[points[&start]][points[&end]] = Some(distance);
        }

        let mut neighbours: Vec<Vec<_>> = adjacency
            .iter()
            .map(|line| {
                line.iter()
                    .enumerate()
                    .filter_map(|(i, d)| d.map(|_| i))
                    .collect()
            })
            .collect();

        let exit = neighbours.len() - 1;
        if let &[exit_neighbour] = &neighbours[exit][..] {
            // if there is exactly one connection to the exit, we must take it, otherwise
            // we’d be cut off
            let exit_neighbour_neighbours = &mut neighbours[exit_neighbour];
            exit_neighbour_neighbours.retain(|&p| p == exit);
        }

        Self { points, adjacency, neighbours }
    }

    fn longest_path_length(&self, start: CartesianPoint, end: CartesianPoint) -> u64 {
        let start = self.points[&start];
        let end = self.points[&end];
        let mut next_points = Vec::new();
        next_points.push((start, 0, 0));
        let mut max = 0;

        while let Some((mut point, mut path, mut distance)) = next_points.pop() {
            if !has_bit(path, point) {
                set_bit(&mut path, point);
                loop {
                    let mut neighbours = self.neighbours[point]
                        .iter()
                        .copied()
                        .filter(|&p| !has_bit(path, p));

                    let Some(neighbour) = neighbours.next()
                    else {
                        break;
                    };
                    next_points.extend(
                        neighbours.map(|n| (n, path, distance + self.adjacency[point][n].unwrap())),
                    );
                    distance += self.adjacency[point][neighbour].unwrap();
                    point = neighbour;
                    set_bit(&mut path, point);
                }
                if point == end {
                    max = max.max(distance);
                }
            }
        }

        max
    }
}

fn has_bit(n: u64, bit: usize) -> bool {
    debug_assert!(bit < 64);
    (n & (1 << bit)) != 0
}

fn set_bit(n: &mut u64, bit: usize) {
    // this assert makes the program ~5 % faster
    assert!(bit < 64);
    debug_assert!(!has_bit(*n, bit));
    *n |= 1 << bit;
}

fn solve(filename: impl AsRef<Path>, slipperiness: impl Slipperiness) -> u64 {
    let forest = Forest(
        RectangularWorld::<CartesianPoint, Tile>::from_file(filename).unwrap(),
        slipperiness,
    );
    // FIXME: `start` and `end` could be anywhere on the first/last line, but in the
    // example and real input, they’re both at fixed positions.
    let start = CartesianPoint(1, 0);
    let CartesianPoint(size_x, size_y) = forest.0.size();
    let end = CartesianPoint(size_x - 2, size_y - 1);

    let mut junctions = vec![start, end];
    for point in forest
        .iter()
        .filter(|(p, _)| forest.is_walkable(p))
        .map(|(p, _)| p)
    {
        let neighbours = forest.neighbours(point).collect::<Vec<_>>();
        if neighbours.len() > 2 {
            junctions.push(point);
        }
    }

    let distances = junctions
        .iter()
        .flat_map(|&point| {
            forest
                .distances_with(point, |p| junctions.contains(&p))
                .map(move |(end, distance)| ((point, end), u64::try_from(distance).unwrap()))
        })
        .collect();

    let graph = Graph::from_map(distances);
    graph.longest_path_length(start, end)
}

fn main() {
    println!("{}", solve("input", Slippery));
    println!("{}", solve("input", NotSlippery));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn part_1() {
        assert_eq!(solve("input_test", Slippery), 94);
    }

    #[test]
    fn part_2() {
        assert_eq!(solve("input_test", NotSlippery), 154);
    }
}
