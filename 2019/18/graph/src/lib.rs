#![feature(thread_local)]

use std::{
    any::TypeId,
    cmp::Reverse,
    collections::{
        HashMap,
        VecDeque,
    },
    convert::TryInto,
    fmt::Debug,
    hash::{
        BuildHasher,
        Hash,
    },
    iter::from_fn,
};

use fnv::{
    FnvHashMap,
    FnvHashSet,
};
use im_rc::{
    vector::RRBPool,
    Vector,
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

    fn canonicalise_point(&self, p: &Self::Point) -> Self::Point {
        p.clone()
    }

    fn is_reachable(&self, start: &Self::Point, end: &Self::Point) -> bool
    where
        <Self as World>::Point: 'static,
    {
        self.walk_cells_breadth_first(start)
            .into_iter()
            .any(|path| path.last() == Some(end))
    }

    fn is_walkable(&self, p: &Self::Point) -> bool {
        self.get(p).as_ref().map_or(false, Tile::is_walkable)
    }

    fn distance(&self, start: &Self::Point, end: &Self::Point) -> Distance
    where
        <Self as World>::Point: 'static,
    {
        self.walk_cells_breadth_first(start)
            .into_iter()
            .find_map(|path| {
                if path.last() == Some(end) {
                    Some(path.len() as _)
                }
                else {
                    None
                }
            })
            .into()
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

pub trait Tile: Clone {
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

impl TryInto<u64> for Distance {
    type Error = Unreachable;

    fn try_into(self) -> Result<u64, Self::Error> {
        Ok(self.0 .0.ok_or(Unreachable)?.0)
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Unreachable;
