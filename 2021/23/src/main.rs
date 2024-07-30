#![feature(type_alias_impl_trait)]

use std::collections::BTreeMap;
use std::collections::BinaryHeap;
use std::collections::HashMap;
use std::error::Error;
use std::marker::PhantomData;

use graph::CartesianPoint;
use graph::Distance;
use graph::RectangularWorld;
use graph::Tile as _;
use graph::World;
use rustc_hash::FxHashMap;

type Burrow = RectangularWorld<graph::CartesianPoint, Tile>;

#[derive(Eq, PartialEq, Copy, Clone, Debug, PartialOrd, Ord, Hash, Default)]
enum Tile {
    #[default]
    Wall,
    Empty,
    Amphipod(char),
}

impl Tile {
    fn is_at_destination(self, point: CartesianPoint) -> bool {
        match self {
            Tile::Amphipod('A') => point.0 == 3,
            Tile::Amphipod('B') => point.0 == 5,
            Tile::Amphipod('C') => point.0 == 7,
            Tile::Amphipod('D') => point.0 == 9,
            _ => unreachable!(),
        }
    }

    fn is_amphipod(self) -> bool {
        matches!(self, Tile::Amphipod(_))
    }

    fn cost(self) -> u64 {
        match self {
            Tile::Amphipod('A') => 1,
            Tile::Amphipod('B') => 10,
            Tile::Amphipod('C') => 100,
            Tile::Amphipod('D') => 1000,
            _ => unreachable!(),
        }
    }

    fn target_x(self) -> usize {
        match self {
            Tile::Amphipod('A') => 3,
            Tile::Amphipod('B') => 5,
            Tile::Amphipod('C') => 7,
            Tile::Amphipod('D') => 9,
            _ => unreachable!(),
        }
    }

    fn has_destination(&self, to: CartesianPoint) -> bool {
        self.target_x() == to.0
    }
}

#[derive(Debug)]
struct Invalid(#[expect(dead_code)] char);

impl graph::Tile for Tile {
    fn is_walkable(&self) -> bool {
        matches!(self, Tile::Empty)
    }
}

impl TryFrom<char> for Tile {
    type Error = Invalid;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        Ok(match value {
            '#' | ' ' => Tile::Wall,
            '.' => Tile::Empty,
            c if "ABCD".contains(c) => Tile::Amphipod(c),
            c => return Err(Invalid(c)),
        })
    }
}

fn is_hallway(point: CartesianPoint) -> bool {
    point.1 == 1
}

fn can_move<const N: usize>(
    burrow: &Burrow,
    from: CartesianPoint,
    to: CartesianPoint,
    target_positions: [CartesianPoint; N],
) -> Option<Distance> {
    if is_hallway(from) && is_hallway(to) {
        return None;
    }

    if !burrow.get(&to).unwrap().is_walkable() {
        return None;
    }

    let start_tile = burrow.get(&from).unwrap();
    assert!(start_tile.is_amphipod());

    if !is_hallway(to) {
        let below_target_positions = &target_positions[to.1 - 2 + 1..];
        if !start_tile.has_destination(to)
            || below_target_positions.iter().any(|point| {
                let tile = burrow.get(point).unwrap();
                tile.is_walkable() || !tile.has_destination(to)
            })
        {
            return None;
        }
    }

    if !is_hallway(from) {
        let below_start_positions = &target_positions
            .map(|CartesianPoint(_, y)| CartesianPoint(from.0, y))[from.1 - 2 + 1..];
        if start_tile.has_destination(from)
            && below_start_positions.iter().all(|point| {
                let tile = burrow.get(point).unwrap();
                tile.is_amphipod() && tile.has_destination(to)
            })
        {
            return None;
        }
    }

    Some(burrow.distance(&from, &to))
}

#[derive(Eq, PartialEq)]
struct NextStep(u64, Burrow);

impl PartialOrd for NextStep {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for NextStep {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0).reverse()
    }
}

fn put_possible_next_steps<const N: usize>(
    next_steps: &mut BinaryHeap<NextStep>,
    burrow: &Burrow,
    seen: &mut FxHashMap<BTreeMap<CartesianPoint, Tile>, u64>,
    previous_distance: u64,
    side_room_y_positions: [usize; N],
) {
    for (from, &tile) in burrow.iter() {
        if !tile.is_amphipod() {
            continue;
        }
        let target_positions = side_room_y_positions.map(|y| CartesianPoint(tile.target_x(), y));
        for to in [(1, 1), (2, 1), (4, 1), (6, 1), (8, 1), (10, 1), (11, 1)]
            .map(|(x, y)| CartesianPoint(x, y))
            .into_iter()
            .chain(target_positions)
        {
            if let Some(Ok(distance)) =
                can_move(burrow, from, to, target_positions).map(u64::try_from)
            {
                let mut new_burrow = burrow.clone();
                let from_tile = new_burrow.get(&from).unwrap();
                new_burrow.insert(to, from_tile);
                new_burrow.insert(from, Tile::Empty);
                let amphipods = new_burrow
                    .iter()
                    .filter(|(_, &tile)| tile.is_amphipod())
                    .map(|(p, &t)| (p, t))
                    .collect();
                let total_distance = distance * from_tile.cost() + previous_distance;
                match seen.get_mut(&amphipods) {
                    None => {
                        seen.insert(amphipods, total_distance);
                        next_steps.push(NextStep(total_distance, new_burrow));
                    }
                    Some(d) =>
                        if total_distance < *d {
                            *d = total_distance;
                            next_steps.push(NextStep(total_distance, new_burrow));
                        },
                }
            }
        }
    }
}

fn all_at_destination(burrow: &Burrow) -> bool {
    burrow
        .iter()
        .filter(|(_, &tile)| tile.is_amphipod())
        .all(|(point, &tile)| tile.is_at_destination(point))
}

fn solve<const N: usize>(burrow: &Burrow, target_positions: [usize; N]) -> u64 {
    let mut next_steps = BinaryHeap::new();
    let mut seen = HashMap::default();
    put_possible_next_steps(&mut next_steps, burrow, &mut seen, 0, target_positions);

    loop {
        let NextStep(distance, burrow) = next_steps.pop().unwrap();
        let amphipods = burrow
            .iter()
            .filter(|(_, &tile)| tile.is_amphipod())
            .map(|(p, &t)| (p, t))
            .collect();
        if seen.get(&amphipods) > Some(&distance) {
            continue;
        }

        if all_at_destination(&burrow) {
            break distance;
        }
        put_possible_next_steps(
            &mut next_steps,
            &burrow,
            &mut seen,
            distance,
            target_positions,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_part_1()
    where
        Burrow:,
    {
        assert_eq!(
            solve(
                &Burrow::from_nonrectangular_file("input_test").unwrap(),
                [2, 3],
            ),
            12521,
        );
    }

    #[test]
    fn test_part_2()
    where
        Burrow:,
    {
        assert_eq!(
            solve(
                &Burrow::from_nonrectangular_file("input_test_2").unwrap(),
                [2, 3, 4, 5],
            ),
            44169,
        );
    }
}

type ActuallyUnit<T> = <Use<T> as HasUnit>::Unit;

struct Use<T>(PhantomData<T>);

trait HasUnit {
    type Unit;
}

impl<T> HasUnit for Use<T> {
    type Unit = ();
}

// Rust PR 112652 requires that TAITs are mentioned in the signature in this
// case, however we can’t use a `where` clause with empty bounds here as `main`
// cannot be constrained by a `where`. So we use this slightly silly workaround.
fn main() -> Result<ActuallyUnit<Burrow>, Box<dyn Error>> {
    println!(
        "{}",
        solve(&Burrow::from_nonrectangular_file("input")?, [2, 3]),
    );
    println!(
        "{}",
        solve(
            &Burrow::from_nonrectangular_file("input_part_2")?,
            [2, 3, 4, 5],
        ),
    );
    Ok(())
}
