#![allow(mixed_script_confusables)]

use std::collections::VecDeque;
use std::io;
use std::path::Path;

use graph::Point as _;
use graph::ReadExt as _;
use graph::RectangularWorld;
use graph::Tile as _;
use graph::World;

const DISTANCE_PART_2: u64 = 26501365;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Tile {
    Start,
    Rock,
    Soil,
}

impl TryFrom<char> for Tile {
    type Error = char;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        match value {
            'S' => Ok(Tile::Start),
            '.' => Ok(Tile::Soil),
            '#' => Ok(Tile::Rock),
            _ => Err(value),
        }
    }
}

impl graph::Tile for Tile {
    fn is_walkable(&self) -> bool {
        matches!(self, Tile::Start | Tile::Soil)
    }
}

type Garden = graph::RectangularWorld<graph::CartesianPoint, Tile>;

fn part_1(garden: &Garden, n: u64) -> u64 {
    let start = garden.find(&Tile::Start).unwrap();
    let mut reachable_neighbours = vec![false; garden.len()];
    garden
        .walk_cells_breadth_first(&start)
        .filter_map(|path| {
            let len = (path.len() as u64).saturating_sub(1);
            if len < n && len % 2 == 0 {
                path.last().cloned()
            }
            else {
                None
            }
        })
        .flat_map(|p| p.neighbours())
        .filter(|p| garden.get(p).is_some_and(|tile| tile.is_walkable()))
        .for_each(|p| reachable_neighbours[garden.index(&p)] = true);
    reachable_neighbours.iter().map(|&b| b as u64).sum()
}

type Point = (i64, i64);

#[derive(Debug, Clone)]
struct InfiniteGarden {
    garden: RectangularWorld<Point, Tile>,
    precomputed_m: u64,
}

impl World for InfiniteGarden {
    type Point = Point;
    type Tile = Tile;

    fn get(&self, &(x, y): &Self::Point) -> Option<Self::Tile> {
        let (size_x, size_y) = self.garden.size();
        self.garden.get(&(
            fastmod::fastmod_s32(x as _, self.precomputed_m, size_x as i32).into(),
            fastmod::fastmod_s32(y as _, self.precomputed_m, size_y as i32).into(),
        ))
    }

    fn iter(&self) -> impl Iterator<Item = (Self::Point, &Self::Tile)> {
        self.garden.iter()
    }
}

impl InfiniteGarden {
    fn from_file(filename: impl AsRef<Path>) -> io::Result<Self> {
        let garden = RectangularWorld::from_file(filename)?;
        let (x, y) = garden.size();
        assert_eq!(x, y);
        let precomputed_m = fastmod::compute_m_s32(i32::try_from(x).unwrap());
        Ok(Self { garden, precomputed_m })
    }

    fn find_deltas(&self, start: Point, total_distance: u64) -> Deltas {
        let size = self.garden.size().0 as u64;
        let bounding_box_side_length = size as usize * 3 * 2 * 2;

        let index = |(x, y)| {
            let x = (x as usize).wrapping_add(bounding_box_side_length / 2);
            let y = (y as usize).wrapping_add(bounding_box_side_length / 2);
            y * bounding_box_side_length + x
        };

        let mut total_at_output_distances = Vec::new();
        let mut next_output_distance = total_distance % size;

        let mut visited = vec![false; bounding_box_side_length.pow(2)];
        let mut reachable_neighbours = vec![false; bounding_box_side_length.pow(2)];

        let mut next_points = VecDeque::new();
        next_points.push_back((start, 0));

        while let Some((point, distance)) = next_points.pop_front() {
            if distance > next_output_distance {
                next_output_distance += 2 * size;
                total_at_output_distances
                    .push(reachable_neighbours.iter().map(|&b| b as u64).sum());

                if total_at_output_distances.len() == 3 {
                    let &[δ1, δ2] = &total_at_output_distances
                        .iter()
                        .zip(&total_at_output_distances[1..])
                        .map(|(a, b)| b - a)
                        .collect::<Vec<_>>()[..]
                    else {
                        unreachable!()
                    };
                    return Deltas {
                        reachable_tiles_at_start_offset: total_at_output_distances[0],
                        δ: δ1,
                        δδ: δ2 - δ1,
                    };
                }
            }

            if distance % 2 != total_distance % 2 {
                self.neighbours(point)
                    .filter(|p| self.is_walkable(p))
                    .for_each(|neighbour| {
                        reachable_neighbours[index(neighbour)] = true;
                    })
            }

            if !visited[index(point)] {
                visited[index(point)] = true;
                let neighbours = self
                    .neighbours(point)
                    .filter(|&neighbour| !visited[index(neighbour)])
                    .map(|p| self.canonicalise_point(&p))
                    .map(|p| (p, distance + self.cost(&p)));
                next_points.extend(neighbours);
            }
        }

        unreachable!()
    }
}

struct Deltas {
    reachable_tiles_at_start_offset: u64,
    δ: u64,
    δδ: u64,
}

fn part_2(garden: &InfiniteGarden, total_distance: u64) -> u64 {
    let start = garden.find(&Tile::Start).unwrap();
    let size = garden.garden.size().0 as u64;
    let start_offset = total_distance % size;
    assert_eq!((total_distance - start_offset) % (2 * size), 0);
    let repeats = (total_distance - start_offset) / (2 * size);
    let Deltas {
        reachable_tiles_at_start_offset: reachable_at_start_offset,
        mut δ,
        δδ,
    } = garden.find_deltas(start, total_distance);
    let mut reachable = reachable_at_start_offset;
    for _ in 0..repeats {
        reachable += δ;
        δ += δδ;
    }
    reachable
}

/// Direct port of the relevant parts of the [`fastmod`](https://github.com/lemire/fastmod)
/// library.
///
/// [`fastmod`](https://github.com/lemire/fastmod) is licensed under the Apache License,
/// Version 2.0, Copyright 2018 Daniel Lemire. License text available at
/// <https://www.apache.org/licenses/LICENSE-2.0.txt>.
///
/// See also: D. Lemire, O. Kaser, and N. Kurz, Faster Remainder by Direct
/// Computation, 2018. <https://arxiv.org/abs/1902.01961>
mod fastmod {
    pub fn compute_m_s32(d: i32) -> u64 {
        if d == i32::MIN {
            panic!("`d` cannot be `i32::MIN`");
        }
        let d = i64::from(d).unsigned_abs();
        u64::MAX / d + 1 + if d.is_power_of_two() { 1 } else { 0 }
    }

    pub fn mul_128_u32(lowbits: u64, d: u32) -> u64 {
        let lowbits = u128::from(lowbits);
        let d = u128::from(d);
        u64::try_from((lowbits * d) >> 64).unwrap()
    }

    pub fn fastmod_s32(a: i32, m: u64, positive_d: i32) -> i32 {
        debug_assert!(positive_d > 0);
        let lowbits = m.wrapping_mul(a as u64);
        let highbits = mul_128_u32(lowbits, positive_d as u32) as i32;
        let result = highbits - ((positive_d - 1) & (a >> 31));
        if result < 0 {
            positive_d + result
        }
        else {
            result
        }
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let garden = Garden::from_file("input")?;
    println!("{}", part_1(&garden, 64));

    let infinite_garden = InfiniteGarden::from_file("input")?;
    println!("{}", part_2(&infinite_garden, DISTANCE_PART_2));

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_part_1() -> Result<(), Box<dyn std::error::Error>> {
        let garden = Garden::from_file("input_test")?;
        assert_eq!(part_1(&garden, 6), 16);
        Ok(())
    }
}
