#![feature(hash_extract_if)]
#![feature(integer_sign_cast)]

use std::io;
use std::iter::from_fn;
use std::path::Path;

use graph::CartesianPoint as Point;
use graph::ReadExt as _;
use graph::RectangularWorld;
use graph::World as _;
use rustc_hash::FxHashSet;

#[derive(Debug)]
struct Garden {
    plots: RectangularWorld<Point, u8>,
    regions: Vec<FxHashSet<Point>>,
}

fn find_region_containing(plots: &RectangularWorld<Point, u8>, p: Point) -> FxHashSet<Point> {
    let plant_ty = plots.get(&p).unwrap();
    let mut to_visit = vec![p];
    let mut region = FxHashSet::default();
    region.insert(p);
    while let Some(p) = to_visit.pop() {
        for neighbour in plots.neighbours(p) {
            if plots.get(&neighbour) == Some(plant_ty) && !region.contains(&neighbour) {
                region.insert(neighbour);
                to_visit.push(neighbour);
            }
        }
    }
    region
}

fn read_input(filename: impl AsRef<Path>) -> io::Result<Garden> {
    let plots = RectangularWorld::from_file(filename)?;

    let mut not_in_any_region_yet = plots.points().collect::<FxHashSet<_>>();
    let regions = from_fn(|| {
        let start = not_in_any_region_yet.extract_if(|_| true).next()?;
        let region = find_region_containing(&plots, start);
        for p in &region {
            not_in_any_region_yet.remove(p);
        }
        Some(region)
    })
    .collect();

    Ok(Garden { plots, regions })
}

fn border_len(plots: &RectangularWorld<Point, u8>, region: &FxHashSet<Point>) -> usize {
    let plant_ty = plots.get(region.iter().next().unwrap()).unwrap();
    region
        .iter()
        .flat_map(|p| p.wrapping_neighbours())
        .filter(|p| plots.get(p) != Some(plant_ty))
        .count()
}

fn part_1(garden: &Garden) -> usize {
    garden
        .regions
        .iter()
        .map(|region| region.len() * border_len(&garden.plots, region))
        .sum()
}

fn border_tiles(region: &FxHashSet<Point>) -> FxHashSet<Point> {
    let scale = 3;
    region
        .iter()
        .flat_map(|&Point(x, y)| {
            (0..scale)
                .flat_map(move |dx| (0..scale).map(move |dy| Point(x * scale + dx, y * scale + dy)))
        })
        .filter(|p| {
            p.wrapping_neighbours()
                .any(|Point(x, y)| !region.contains(&Point(x / scale, y / scale)))
        })
        .collect()
}

const DIRECTIONS: [(isize, isize); 4] = [(1, 0), (0, 1), (-1, 0), (0, -1)];

fn direction(index: isize) -> (isize, isize) {
    DIRECTIONS[index
        .rem_euclid(DIRECTIONS.len().cast_signed())
        .cast_unsigned()]
}

fn left(index: isize) -> (isize, isize) {
    direction(index - 1)
}

fn forward(index: isize) -> (isize, isize) {
    direction(index)
}

fn right(index: isize) -> (isize, isize) {
    direction(index + 1)
}

fn side_count(region: &FxHashSet<Point>) -> usize {
    let mut border = border_tiles(region);
    let mut result = 0;
    while let Some(&start) = border.iter().min_by_key(|Point(x, y)| (y, x)) {
        let mut p = start;
        let mut direction = 0;
        loop {
            border.remove(&p);

            if border.contains(&(p + left(direction))) {
                result += 1;
                direction -= 1;
            }
            else if border.contains(&(p + forward(direction))) {
                if p == start {
                    result += 1;
                }
            }
            else if border.contains(&(p + right(direction))) {
                result += 1;
                direction += 1;
            }
            else {
                break;
            }

            p += forward(direction);

            if p == start {
                break;
            }
        }
    }
    result
}

fn part_2(garden: &Garden) -> usize {
    garden
        .regions
        .iter()
        .map(|region| region.len() * side_count(region))
        .sum()
}

fn main() -> io::Result<()> {
    let garden = read_input("input")?;
    println!("{}", part_1(&garden));
    println!("{}", part_2(&garden));
    Ok(())
}
