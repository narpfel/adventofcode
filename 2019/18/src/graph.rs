/// This is intended to be useful for more than just one puzzle.
use std::{
    cmp::Reverse,
    collections::{
        HashMap,
        HashSet,
        VecDeque,
    },
    fmt::Debug,
    hash::Hash,
};

// TODO: Formulate in terms of edges and vertices. Maybe use some kind of
// adjacency matrix/hash map?

pub trait World: Clone {
    type Point: Point;
    type Tile: Tile;

    fn get(&self, p: &Self::Point) -> Option<Self::Tile>;

    fn contains(&self, p: &Self::Point) -> bool {
        self.get(p).is_some()
    }

    fn is_reachable(&self, start: &Self::Point, end: &Self::Point) -> bool {
        self.walk_cells_breadth_first(start)
            .into_iter()
            .any(|(ref p, _)| p == end)
    }

    fn is_walkable(&self, p: &Self::Point) -> bool {
        self.get(p).as_ref().map_or(false, Tile::is_walkable)
    }

    fn distance(&self, start: &Self::Point, end: &Self::Point) -> Distance {
        self.walk_cells_breadth_first(start)
            .into_iter()
            .find_map(|(p, d)| if &p == end { Some(d.len() as _) } else { None })
            .into()
    }

    fn neighbours(&self, p: Self::Point) -> Vec<Self::Point> {
        (p.neighbours())
            .into_iter()
            .filter(|neighbour| self.is_walkable(neighbour))
            .collect()
    }

    fn walk_cells_breadth_first(
        &self,
        start: &Self::Point,
    ) -> Vec<(Self::Point, Vec<Self::Point>)> {
        let mut visited = HashSet::new();
        visited.insert(start.clone());
        let mut result = vec![];

        let mut next_points = VecDeque::new();
        next_points.push_back((start.clone(), vec![]));

        while let Some((point, path)) = next_points.pop_front() {
            visited.insert(point.clone());
            result.push((point.clone(), path.clone()));
            next_points.extend(
                self.neighbours(point.clone())
                    .iter()
                    .filter(|p| !visited.contains(p))
                    .map(|p| {
                        (p.clone(), {
                            let mut path = path.clone();
                            path.push(p.clone());
                            path
                        })
                    }),
            );
        }

        result
    }
}

pub trait Tile: Clone {
    fn is_walkable(&self) -> bool;
}

impl<Point, Tile> World for HashMap<Point, Tile>
where
    Point: self::Point + Eq + Hash,
    Tile: self::Tile,
{
    type Point = Point;
    type Tile = Tile;

    fn get(&self, p: &Self::Point) -> Option<Self::Tile> {
        HashMap::get(self, p).cloned()
    }
}

// struct<Tile> RectancularWorld {
//     world: Vec<Tile>,
//     width: usize,
//     height: usize;
// }
//
// impl World for RectancularWorld<Tile> {
//     // ...
// }

pub trait Point: PartialEq + Clone + Eq + Hash + Debug {
    fn neighbours(&self) -> Vec<Self>
    where
        Self: Sized;
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Ord, PartialOrd, Default)]
pub struct CartesianPoint(pub usize, pub usize);

impl Point for CartesianPoint {
    fn neighbours(&self) -> Vec<Self> {
        let CartesianPoint(x, y) = *self;
        vec![
            CartesianPoint(x - 1, y),
            CartesianPoint(x + 1, y),
            CartesianPoint(x, y - 1),
            CartesianPoint(x, y + 1),
        ]
    }
}

#[derive(Default, Debug, PartialOrd, Ord, PartialEq, Eq, Copy, Clone)]
pub struct Distance(Reverse<Option<Reverse<u64>>>);

impl Distance {
    pub fn new(distance: u64) -> Distance {
        Distance(Reverse(Some(Reverse(distance))))
    }

    pub fn infinity() -> Distance {
        Self::default()
    }
}

impl From<Option<u64>> for Distance {
    fn from(value: Option<u64>) -> Self {
        value.map_or_else(Distance::infinity, Distance::new)
    }
}
