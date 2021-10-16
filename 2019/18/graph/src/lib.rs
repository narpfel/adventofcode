#![feature(thread_local)]

use std::any::TypeId;
use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::fmt::Debug;
use std::fs::File;
use std::hash::BuildHasher;
use std::hash::Hash;
use std::io;
use std::io::BufRead;
use std::io::BufReader;
use std::iter::from_fn;
use std::path::Path;

use fnv::FnvHashMap;
use fnv::FnvHashSet;
use im_rc::vector::RRBPool;
use im_rc::Vector;

// TODO: Formulate in terms of edges and vertices. Maybe use some kind of
// adjacency matrix/hash map?

pub trait World: Clone {
    type Point: Point;
    type Tile: Tile;

    fn get(&self, p: &Self::Point) -> Option<Self::Tile>;
    fn find(&self, tile: &Self::Tile) -> Option<Self::Point>;

    fn contains(&self, p: &Self::Point) -> bool {
        self.get(p).is_some()
    }

    fn canonicalise_point(&self, p: &Self::Point) -> Self::Point {
        p.clone()
    }

    fn is_reachable(&self, start: &Self::Point, end: &Self::Point) -> bool {
        self.path(start, end).is_some()
    }

    fn is_walkable(&self, p: &Self::Point) -> bool {
        self.get(p).as_ref().map_or(false, Tile::is_walkable)
    }

    fn distance(&self, start: &Self::Point, end: &Self::Point) -> Distance {
        // Don’t include start point
        Distance::from(self.path(start, end).map(|path| path.len() as _)).map(|d| d - 1)
    }

    /// Dijkstra’s algorithm
    fn path(&self, start: &Self::Point, end: &Self::Point) -> Option<Vec<Self::Point>> {
        #[derive(Eq, PartialEq)]
        struct NextPoint<P> {
            distance: Reverse<Distance>,
            point: P,
        }
        impl<P: Eq> PartialOrd for NextPoint<P> {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                self.distance.partial_cmp(&other.distance)
            }
        }
        impl<P: Eq> Ord for NextPoint<P> {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                self.distance.cmp(&other.distance)
            }
        }

        let mut distances = HashMap::new();
        distances.insert(self.canonicalise_point(start), Distance::new(0));
        let mut visited = HashSet::new();
        let mut previous_point = HashMap::new();
        let mut next_points = BinaryHeap::new();
        next_points.push(NextPoint {
            distance: Reverse(Distance::new(0)),
            point: self.canonicalise_point(start),
        });

        while let Some(NextPoint { distance: Reverse(distance), point }) = next_points.pop() {
            visited.insert(point.clone());
            for neighbour in self
                .neighbours(point.clone())
                .filter(|p| self.get(p).is_some() && !visited.contains(p))
                .map(|p| self.canonicalise_point(&p))
            {
                let distance = if !self.is_walkable(&neighbour) {
                    Distance::infinity()
                }
                else {
                    distance.map(|d| d + 1)
                };
                if distances.get(&neighbour).map_or(true, |d| d > &distance) {
                    distances.insert(neighbour.clone(), distance);
                    previous_point.insert(neighbour.clone(), point.clone());
                    next_points.push(NextPoint {
                        distance: Reverse(distance),
                        point: neighbour,
                    });
                }
            }

            if &point == end {
                let mut path = vec![point.clone()];
                let mut point = point.clone();
                while let Some(p) = previous_point.get(&point) {
                    point = p.clone();
                    path.push(point.clone());
                    if &point == start {
                        path.reverse();
                        return Some(path);
                    }
                }
            }
        }

        None
    }

    fn neighbours<'a>(&'a self, point: Self::Point) -> Box<dyn Iterator<Item = Self::Point> + 'a> {
        Box::new(
            point
                .neighbours()
                .into_iter()
                .filter(move |neighbour| self.is_walkable(neighbour)),
        )
    }

    fn walk_cells_breadth_first<'a>(
        &'a self,
        start: &Self::Point,
    ) -> Box<dyn Iterator<Item = Vector<Self::Point>> + 'a>
    where
        <Self as World>::Point: 'static,
    {
        struct Erased(FnvHashMap<TypeId, ErasedPtr>);

        impl Erased {
            fn get<T: 'static>(&mut self) -> &'static RRBPool<T> {
                self.0
                    .entry(TypeId::of::<T>())
                    .or_insert_with(|| ErasedPtr::new(RRBPool::<T>::new(300_000)))
                    .get()
            }
        }

        struct ErasedPtr(*const ());

        impl ErasedPtr {
            fn new<T>(val: T) -> Self {
                ErasedPtr(Box::leak(Box::new(val)) as *const T as _)
            }

            fn get<T>(&self) -> &'static T {
                unsafe { &*(self.0 as *const T) }
            }
        }

        #[thread_local]
        static mut POOL: Option<Erased> = None;
        let pool = unsafe { POOL.get_or_insert_with(|| Erased(FnvHashMap::default())) };

        let mut visited = FnvHashSet::default();
        visited.insert(start.clone());

        let mut next_points = VecDeque::new();
        next_points.push_back((start.clone(), Vector::with_pool(pool.get())));

        Box::new(from_fn(move || {
            next_points.pop_front().map(|(point, path)| {
                visited.insert(point.clone());
                let neighbours = self
                    .neighbours(point)
                    .filter(|p| !visited.contains(p))
                    .map(|p| self.canonicalise_point(&p))
                    .map(|p| {
                        (p.clone(), {
                            let mut path = path.clone();
                            path.push_back(p);
                            path
                        })
                    });
                next_points.extend(neighbours);
                path
            })
        }))
    }
}

pub trait Tile: Clone + PartialEq + Eq {
    fn is_walkable(&self) -> bool;
}

impl<Point, Tile, S> World for HashMap<Point, Tile, S>
where
    Point: self::Point + Eq + Hash,
    Tile: self::Tile,
    S: BuildHasher + Clone,
{
    type Point = Point;
    type Tile = Tile;

    fn get(&self, p: &Self::Point) -> Option<Self::Tile> {
        HashMap::get(self, p).cloned()
    }

    fn find(&self, tile: &Self::Tile) -> Option<Self::Point> {
        self.iter()
            .find(|(_, v)| v == &tile)
            .map(|(k, _)| k.clone())
    }
}

pub trait ReadExt: World {
    fn from_file(path: impl AsRef<Path>) -> Result<Self, io::Error>
    where
        Self::Tile: TryFrom<char>,
        <Self::Tile as TryFrom<char>>::Error: Debug;
}

impl<Point, Tile> ReadExt for FnvHashMap<Point, Tile>
where
    Point: self::Point + Eq + Hash + Cartesian,
    Tile: self::Tile + TryFrom<char>,
{
    fn from_file(path: impl AsRef<Path>) -> Result<Self, io::Error>
    where
        <Self::Tile as TryFrom<char>>::Error: Debug,
    {
        let f = File::open(path)?;
        let reader = BufReader::new(f);

        let mut maze = Self::default();
        for (y, line) in reader.lines().enumerate() {
            for (x, c) in line?.chars().enumerate() {
                maze.insert(
                    Point::from_xy((x, y)),
                    c.try_into().map_err(|err| {
                        io::Error::new(
                            io::ErrorKind::Other,
                            format!("invalid char: {} ({:?})", c, err),
                        )
                    })?,
                );
            }
        }

        Ok(maze)
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

pub trait Cartesian {
    fn from_xy(xy: (usize, usize)) -> Self;
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Ord, PartialOrd, Default)]
pub struct CartesianPoint(pub usize, pub usize);

impl CartesianPoint {
    pub fn is_direct_neighbour(self, CartesianPoint(x2, y2): CartesianPoint) -> bool {
        fn absolute_difference(x: usize, y: usize) -> usize {
            if x > y {
                x - y
            }
            else {
                y - x
            }
        }

        let CartesianPoint(x1, y1) = self;
        if x1 == x2 {
            absolute_difference(y1, y2) == 1
        }
        else if y1 == y2 {
            absolute_difference(x1, x2) == 1
        }
        else {
            false
        }
    }
}

impl Point for CartesianPoint {
    fn neighbours(&self) -> Vec<Self> {
        let CartesianPoint(x, y) = *self;
        let mut neighbours = Vec::with_capacity(4);
        if let Some(x) = x.checked_sub(1) {
            neighbours.push(CartesianPoint(x, y));
        }
        neighbours.push(CartesianPoint(x + 1, y));
        if let Some(y) = y.checked_sub(1) {
            neighbours.push(CartesianPoint(x, y));
        }
        neighbours.push(CartesianPoint(x, y + 1));
        neighbours
    }
}

impl Cartesian for CartesianPoint {
    fn from_xy((x, y): (usize, usize)) -> Self {
        Self(x, y)
    }
}

impl Point for (i64, i64) {
    fn neighbours(&self) -> Vec<Self>
    where
        Self: Sized,
    {
        let (x, y) = *self;
        vec![(x - 1, y), (x + 1, y), (x, y - 1), (x, y + 1)]
    }
}
impl Cartesian for (i64, i64) {
    fn from_xy((x, y): (usize, usize)) -> Self {
        (x as _, y as _)
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

    fn map(self, f: impl FnOnce(u64) -> u64) -> Self {
        Distance(Reverse(self.0 .0.map(|Reverse(d)| Reverse(f(d)))))
    }
}

impl From<Option<u64>> for Distance {
    fn from(value: Option<u64>) -> Self {
        value.map_or_else(Distance::infinity, Distance::new)
    }
}

impl TryInto<u64> for Distance {
    type Error = Unreachable;

    fn try_into(self) -> Result<u64, Self::Error> {
        Ok(self.0 .0.ok_or(Unreachable)?.0)
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Unreachable;
