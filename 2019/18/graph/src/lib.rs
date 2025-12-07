#![feature(associated_type_defaults)]
#![feature(thread_local)]

use std::any::TypeId;
use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::fmt::Debug;
use std::fs::File;
use std::hash::BuildHasher;
use std::hash::Hash;
use std::io;
use std::io::BufRead;
use std::io::BufReader;
use std::iter::from_fn;
use std::marker::PhantomData;
use std::path::Path;
use std::sync::LazyLock;
use std::sync::Mutex;

use fnv::FnvHashMap;
use fnv::FnvHashSet;
use im_rc::vector::RRBPool;
use im_rc::Vector;
pub use rustc_hash::FxHashMap;

// TODO: Formulate in terms of edges and vertices. Maybe use some kind of
// adjacency matrix/hash map?

pub trait World: Clone {
    type Point: Point;
    type Tile: Tile;
    type PointOrder: self::PointOrder = Unordered;

    fn get(&self, p: &Self::Point) -> Option<Self::Tile>;
    fn iter(&self) -> impl Iterator<Item = (Self::Point, &Self::Tile)>;

    fn points(&self) -> impl Iterator<Item = Self::Point> {
        self.iter().map(|(p, _)| p)
    }

    fn tiles(&self) -> impl Iterator<Item = &Self::Tile> {
        self.iter().map(|(_, tile)| tile)
    }

    fn find_all<'a>(&'a self, tile: &'a Self::Tile) -> impl Iterator<Item = Self::Point> {
        self.iter().filter_map(move |(p, t)| {
            if t == tile {
                Some(p)
            }
            else {
                None
            }
        })
    }

    fn find(&self, tile: &Self::Tile) -> Option<Self::Point> {
        self.find_all(tile).next()
    }

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
        self.get(p).as_ref().is_some_and(Tile::is_walkable)
    }

    fn distance(&self, start: &Self::Point, end: &Self::Point) -> Distance {
        self.distance_with(start, |p| p == end)
    }

    fn distance_with(
        &self,
        start: &Self::Point,
        is_at_end: impl FnMut(&Self::Point) -> bool,
    ) -> Distance {
        // Don’t include start point
        Distance::from(self.path_with(start, is_at_end).map(|path| {
            path.array_windows()
                .map(|[from, to]| self.cost(from, to))
                .sum()
        }))
    }

    fn path(&self, start: &Self::Point, end: &Self::Point) -> Option<Vec<Self::Point>> {
        self.path_with(start, |p| p == end)
    }

    /// Dijkstra’s algorithm
    fn path_with(
        &self,
        start: &Self::Point,
        mut is_at_end: impl FnMut(&Self::Point) -> bool,
    ) -> Option<Vec<Self::Point>> {
        let mut distance_prev = FnvHashMap::default();
        distance_prev.insert(self.canonicalise_point(start), (0, None));
        let mut next_points = MonotonicPriorityQueue::<Self::PointOrder, Self::Point>::default();
        next_points.push(0, self.canonicalise_point(start));

        while let Some((distance, point)) = next_points.pop() {
            for neighbour in self
                .neighbours(point.clone())
                .map(|p| self.canonicalise_point(&p))
            {
                if !self.is_walkable(&neighbour) {
                    continue;
                }
                let distance = distance + self.cost(&point, &neighbour);
                if distance_prev
                    .get(&neighbour)
                    .is_none_or(|(d, _)| d > &distance)
                {
                    distance_prev.insert(neighbour.clone(), (distance, Some(point.clone())));
                    next_points.push(distance, neighbour);
                }
            }

            if is_at_end(&point) {
                let mut path = vec![point.clone()];
                let mut point = point.clone();
                while let Some((_, Some(p))) = distance_prev.get(&point) {
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

    fn neighbours(&self, point: Self::Point) -> impl Iterator<Item = Self::Point> {
        point
            .neighbours()
            .filter(move |neighbour| self.is_walkable(neighbour))
    }

    fn walk_cells_breadth_first(
        &self,
        start: &Self::Point,
    ) -> impl Iterator<Item = Vector<Self::Point>>
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
        static POOL: LazyLock<Mutex<Erased>> =
            LazyLock::new(|| Mutex::new(Erased(FnvHashMap::default())));
        let mut pool = POOL.try_lock().unwrap();

        let mut visited = FnvHashSet::default();

        let mut next_points = VecDeque::new();
        next_points.push_back((start.clone(), Vector::with_pool(pool.get())));

        from_fn(move || {
            while let Some((point, path)) = next_points.pop_front() {
                if !visited.contains(&point) {
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
                    return Some(path);
                }
            }
            None
        })
    }

    fn cost(&self, _from: &Self::Point, _to: &Self::Point) -> u64 {
        1
    }

    fn all_reachable_points(&self, start: Self::Point) -> FnvHashSet<Self::Point> {
        let mut seen = FnvHashSet::default();
        let mut todo = VecDeque::from([start]);

        while let Some(p) = todo.pop_front() {
            if seen.contains(&p) {
                continue;
            }
            seen.insert(p.clone());
            todo.extend(self.neighbours(p).map(|p| self.canonicalise_point(&p)));
        }
        seen
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
    type PointOrder = Unordered;
    type Tile = Tile;

    fn get(&self, p: &Self::Point) -> Option<Self::Tile> {
        HashMap::get(self, p).cloned()
    }

    fn iter(&self) -> impl Iterator<Item = (Self::Point, &Self::Tile)> {
        HashMap::iter(self).map(|(point, tile)| (point.clone(), tile))
    }
}

pub trait ReadExt: World {
    fn from_file(path: impl AsRef<Path>) -> Result<Self, io::Error>
    where
        Self::Tile: TryFrom<char>,
        <Self::Tile as TryFrom<char>>::Error: Debug;
}

impl<Point, Tile, State> ReadExt for HashMap<Point, Tile, State>
where
    Point: self::Point + Eq + Hash + Cartesian,
    Tile: self::Tile + TryFrom<char>,
    State: BuildHasher + Default + Clone,
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
                    c.try_into()
                        .map_err(|err| io::Error::other(format!("invalid char: {c} ({err:?})")))?,
                );
            }
        }

        Ok(maze)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RectangularWorld<Point, Tile, PointOrder = Unordered> {
    world: Vec<Tile>,
    width: usize,
    _point: PhantomData<Point>,
    _point_order: PhantomData<fn(PointOrder)>,
}

impl<Point, Tile, PointOrder> RectangularWorld<Point, Tile, PointOrder>
where
    Point: Cartesian,
    Tile: crate::Tile,
{
    pub fn from_map(world: FnvHashMap<CartesianPoint, Tile>) -> Self {
        Self::from_map_or_else(world, |_| panic!("world is not rectangular"))
    }

    pub fn from_map_or_else(
        world: FnvHashMap<CartesianPoint, Tile>,
        mut or_else: impl FnMut(CartesianPoint) -> Tile,
    ) -> Self {
        let width = world.keys().map(|CartesianPoint(x, _)| x).max().unwrap() + 1;
        let height = world.keys().map(|CartesianPoint(_, y)| y).max().unwrap() + 1;
        let mut tiles = vec![];
        for y in 0..height {
            for x in 0..width {
                tiles.push(
                    World::get(&world, &CartesianPoint(x, y))
                        .unwrap_or_else(|| or_else(CartesianPoint(x, y)))
                        .to_owned(),
                );
            }
        }
        Self {
            world: tiles,
            width,
            _point: PhantomData,
            _point_order: PhantomData,
        }
    }

    pub fn from_nonrectangular_file(path: impl AsRef<Path>) -> Result<Self, io::Error>
    where
        Tile: TryFrom<char> + Default,
        <Tile as TryFrom<char>>::Error: Debug,
    {
        Ok(Self::from_map_or_else(ReadExt::from_file(path)?, |_| {
            Tile::default()
        }))
    }

    pub fn iter(&self) -> impl Iterator<Item = (Point, &Tile)> {
        self.world
            .iter()
            .enumerate()
            .map(|(i, tile)| (Point::from_xy((i % self.width, i / self.width)), tile))
    }

    pub fn tiles(&self) -> impl Iterator<Item = &Tile> {
        self.world.iter()
    }

    pub fn insert(&mut self, p: Point, tile: Tile) -> Option<Tile> {
        let old = self.get_mut(p);
        old.map(|old_tile| std::mem::replace(old_tile, tile))
    }

    pub fn get_mut(&mut self, p: Point) -> Option<&mut Tile> {
        let index = self.index(&p);
        self.world.get_mut(index)
    }

    pub fn index(&self, p: &Point) -> usize {
        let (x, y) = p.to_xy();
        x + y * self.width
    }

    pub fn len(&self) -> usize {
        self.world.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn lines(&self) -> impl Iterator<Item = &[Tile]> {
        self.world.chunks(self.width)
    }

    pub fn size(&self) -> Point {
        Point::from_xy((self.width, self.len() / self.width))
    }

    pub fn points(&self) -> impl Iterator<Item = Point> + use<'_, Point, Tile, PointOrder> {
        self.iter().map(|(p, _)| p)
    }
}

impl<Point, Tile, PointOrder> World for RectangularWorld<Point, Tile, PointOrder>
where
    Point: Cartesian + crate::Point,
    Tile: crate::Tile,
    PointOrder: self::PointOrder,
{
    type Point = Point;
    type PointOrder = PointOrder;
    type Tile = Tile;

    fn get(&self, p: &Self::Point) -> Option<Self::Tile> {
        let (width, height) = self.size().to_xy();
        let (x, y) = p.to_xy();
        if x >= width || y >= height {
            None
        }
        else {
            self.world.get(self.index(p)).cloned()
        }
    }

    fn iter(&self) -> impl Iterator<Item = (Self::Point, &Self::Tile)> {
        RectangularWorld::iter(self)
    }

    fn path(&self, start: &Self::Point, end: &Self::Point) -> Option<Vec<Self::Point>> {
        let mut distance_prev = vec![None; self.len()];
        distance_prev[self.index(&self.canonicalise_point(start))] = Some((0, None));
        let mut next_points = MonotonicPriorityQueue::<Self::PointOrder, Self::Point>::default();
        next_points.push(0, self.canonicalise_point(start));

        while let Some((distance, point)) = next_points.pop() {
            for neighbour in self
                .neighbours(point.clone())
                .map(|p| self.canonicalise_point(&p))
            {
                if !self.is_walkable(&neighbour) {
                    continue;
                }
                let distance = distance + self.cost(&point, &neighbour);
                if distance_prev[self.index(&neighbour)]
                    .as_ref()
                    .is_none_or(|(d, _)| d > &distance)
                {
                    distance_prev[self.index(&neighbour)] = Some((distance, Some(point.clone())));
                    next_points.push(distance, neighbour);
                }
            }

            if &point == end {
                let mut path = vec![point.clone()];
                let mut point = point.clone();
                while let Some((_, Some(p))) = &distance_prev[self.index(&point)] {
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
}

pub trait PointOrder: Clone {
    type Container<T>: PriorityQueueContainer<Item = T>
    where
        T: Ord;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Unordered;

impl PointOrder for Unordered {
    type Container<T>
        = Vec<T>
    where
        T: Ord;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Ordered;

impl PointOrder for Ordered {
    type Container<T>
        = BinaryHeap<T>
    where
        T: Ord;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ReverseOrdered;

impl PointOrder for ReverseOrdered {
    type Container<T>
        = ReverseBinaryHeap<T>
    where
        T: Ord;
}

pub trait PriorityQueueContainer: Default {
    type Item;

    fn is_empty(&self) -> bool;
    fn push(&mut self, value: Self::Item);
    fn pop(&mut self) -> Option<Self::Item>;
}

impl<T> PriorityQueueContainer for Vec<T> {
    type Item = T;

    fn is_empty(&self) -> bool {
        self.is_empty()
    }

    fn push(&mut self, value: Self::Item) {
        self.push(value)
    }

    fn pop(&mut self) -> Option<Self::Item> {
        self.pop()
    }
}

impl<T> PriorityQueueContainer for BinaryHeap<T>
where
    T: Ord,
{
    type Item = T;

    fn is_empty(&self) -> bool {
        self.is_empty()
    }

    fn push(&mut self, value: Self::Item) {
        self.push(value)
    }

    fn pop(&mut self) -> Option<Self::Item> {
        self.pop()
    }
}

#[derive(Clone)]
pub struct ReverseBinaryHeap<T>(BinaryHeap<Reverse<T>>);

impl<T> Default for ReverseBinaryHeap<T>
where
    T: Ord,
{
    fn default() -> Self {
        Self(BinaryHeap::default())
    }
}

impl<T> PriorityQueueContainer for ReverseBinaryHeap<T>
where
    T: Ord,
{
    type Item = T;

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn push(&mut self, value: T) {
        self.0.push(Reverse(value))
    }

    fn pop(&mut self) -> Option<T> {
        self.0.pop().map(|value| value.0)
    }
}

pub struct MonotonicPriorityQueue<PointOrder: self::PointOrder, T: Ord> {
    min_prio: u64,
    queue: VecDeque<PointOrder::Container<T>>,
    spares: Vec<PointOrder::Container<T>>,
}

impl<PointOrder, T> MonotonicPriorityQueue<PointOrder, T>
where
    PointOrder: self::PointOrder,
    T: Ord,
{
    pub fn new() -> Self {
        Self::default()
    }
}

impl<PointOrder, T> MonotonicPriorityQueue<PointOrder, T>
where
    PointOrder: self::PointOrder,
    T: Ord,
{
    pub fn push(&mut self, priority: u64, value: T) {
        let index = priority.checked_sub(self.min_prio).unwrap() as usize;
        let min_length = index + 1;
        if min_length > self.queue.len() {
            let elements_needed = min_length - self.queue.len();
            let start_index = self.spares.len().saturating_sub(elements_needed);
            let spares = self.spares.drain(start_index..);
            self.queue.extend(spares);
            self.queue
                .resize_with(min_length, PointOrder::Container::default);
        }
        self.queue[index].push(value);
    }

    pub fn pop(&mut self) -> Option<(u64, T)> {
        loop {
            match self.queue.front_mut() {
                Some(bucket) if bucket.is_empty() => {
                    let bucket = self.queue.pop_front();
                    if let Some(bucket) = bucket {
                        self.spares.push(bucket);
                    }
                    self.min_prio += 1;
                }
                Some(bucket) => {
                    break bucket.pop().map(|value| (self.min_prio, value));
                }
                None => {
                    break None;
                }
            }
        }
    }
}

impl<PointOrder, T> Default for MonotonicPriorityQueue<PointOrder, T>
where
    PointOrder: self::PointOrder,
    T: Ord,
{
    fn default() -> Self {
        Self {
            min_prio: 0,
            queue: VecDeque::default(),
            spares: Vec::default(),
        }
    }
}

impl<Point, Tile, PointOrder> ReadExt for RectangularWorld<Point, Tile, PointOrder>
where
    Point: Cartesian + crate::Point,
    Tile: crate::Tile + TryFrom<char>,
    PointOrder: self::PointOrder,
{
    fn from_file(path: impl AsRef<Path>) -> Result<Self, io::Error>
    where
        <Self::Tile as TryFrom<char>>::Error: Debug,
    {
        HashMap::<CartesianPoint, Tile, _>::from_file(path).map(Self::from_map)
    }
}

pub trait Point: PartialEq + Clone + Eq + Hash + Debug + PartialOrd + Ord {
    fn neighbours(self) -> impl Iterator<Item = Self>
    where
        Self: Sized;
}

pub trait Cartesian {
    fn from_xy(xy: (usize, usize)) -> Self;
    fn to_xy(&self) -> (usize, usize);
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Ord, PartialOrd, Default)]
pub struct CartesianPoint(pub usize, pub usize);

impl CartesianPoint {
    pub fn wrapping_neighbours(self) -> impl Iterator<Item = Self> {
        [self + (-1, 0), self + (1, 0), self + (0, -1), self + (0, 1)].into_iter()
    }

    pub fn is_direct_neighbour(self, CartesianPoint(x2, y2): CartesianPoint) -> bool {
        let CartesianPoint(x1, y1) = self;
        if x1 == x2 {
            y2.abs_diff(y1) == 1
        }
        else if y1 == y2 {
            x2.abs_diff(x1) == 1
        }
        else {
            false
        }
    }
}

impl Point for CartesianPoint {
    #[inline]
    fn neighbours(self) -> impl Iterator<Item = Self> {
        let CartesianPoint(x, y) = self;
        let mut neighbours = Vec::with_capacity(4);
        if let Some(x) = x.checked_sub(1) {
            neighbours.push(CartesianPoint(x, y));
        }
        neighbours.push(CartesianPoint(x + 1, y));
        if let Some(y) = y.checked_sub(1) {
            neighbours.push(CartesianPoint(x, y));
        }
        neighbours.push(CartesianPoint(x, y + 1));
        neighbours.into_iter()
    }
}

impl Cartesian for CartesianPoint {
    fn from_xy((x, y): (usize, usize)) -> Self {
        Self(x, y)
    }

    fn to_xy(&self) -> (usize, usize) {
        (self.0, self.1)
    }
}

impl std::ops::Add<(isize, isize)> for CartesianPoint {
    type Output = Self;

    fn add(self, (dx, dy): (isize, isize)) -> Self::Output {
        let Self(x, y) = self;
        Self(x.wrapping_add_signed(dx), y.wrapping_add_signed(dy))
    }
}

impl std::ops::AddAssign<(isize, isize)> for CartesianPoint {
    fn add_assign(&mut self, rhs: (isize, isize)) {
        *self = *self + rhs;
    }
}

impl std::ops::Sub for CartesianPoint {
    type Output = (i64, i64);

    fn sub(self, rhs: Self) -> Self::Output {
        let CartesianPoint(x1, y1) = self;
        let CartesianPoint(x2, y2) = rhs;
        (x1 as i64 - x2 as i64, y1 as i64 - y2 as i64)
    }
}

impl Point for (i64, i64) {
    fn neighbours(self) -> impl Iterator<Item = Self>
    where
        Self: Sized,
    {
        let (x, y) = self;
        [(x - 1, y), (x + 1, y), (x, y - 1), (x, y + 1)].into_iter()
    }
}

impl Cartesian for (i64, i64) {
    fn from_xy((x, y): (usize, usize)) -> Self {
        (x as _, y as _)
    }

    fn to_xy(&self) -> (usize, usize) {
        (self.0 as _, self.1 as _)
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

    pub fn map(self, f: impl FnOnce(u64) -> u64) -> Self {
        Distance(Reverse(self.0 .0.map(|Reverse(d)| Reverse(f(d)))))
    }
}

impl From<usize> for Distance {
    fn from(value: usize) -> Self {
        Distance::new(value.try_into().unwrap())
    }
}

impl From<Option<u64>> for Distance {
    fn from(value: Option<u64>) -> Self {
        value.map_or_else(Distance::infinity, Distance::new)
    }
}

impl TryFrom<Distance> for u64 {
    type Error = Unreachable;

    fn try_from(distance: Distance) -> Result<Self, Self::Error> {
        Ok(distance.0 .0.ok_or(Unreachable)?.0)
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Unreachable;

impl Tile for bool {
    fn is_walkable(&self) -> bool {
        *self
    }
}

impl Tile for u8 {
    fn is_walkable(&self) -> bool {
        true
    }
}
