#![feature(return_position_impl_trait_in_trait)]

use graph::{
    CartesianPoint,
    Point as _,
    ReadExt,
    RectangularWorld,
    World,
};
use itertools::Itertools;

const INITIAL_HITPOINTS: usize = 200;
const ATTACK_STRENGTH: usize = 3;

#[derive(Debug)]
struct InvalidAttackTarget;

#[derive(Debug, PartialEq, Eq)]
enum Winner {
    Goblins,
    Elves,
    ElvesWithLosses,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Tile {
    Wall,
    Empty,
    Goblin(usize),
    Elf(usize),
}

impl Tile {
    fn is_unit(&self) -> bool {
        matches!(self, Tile::Goblin(_) | Tile::Elf(_))
    }

    fn is_enemy(&self, other: &Tile) -> bool {
        matches!(
            (self, other),
            (Tile::Goblin(_), Tile::Elf(_)) | (Tile::Elf(_), Tile::Goblin(_))
        )
    }

    fn health(&self) -> Option<usize> {
        match self {
            Tile::Goblin(hp) | Tile::Elf(hp) => Some(*hp),
            _ => None,
        }
    }

    fn apply_damage(&mut self, damage: usize) -> Result<(), InvalidAttackTarget> {
        match self {
            Tile::Goblin(hp) | Tile::Elf(hp) => match hp.checked_sub(damage) {
                Some(new_hp) if new_hp > 0 => *hp = new_hp,
                _ => *self = Tile::Empty,
            },
            _ => return Err(InvalidAttackTarget),
        }
        Ok(())
    }
}

impl graph::Tile for Tile {
    fn is_walkable(&self) -> bool {
        matches!(self, Tile::Empty)
    }
}

impl TryFrom<char> for Tile {
    type Error = char;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        Ok(match value {
            '#' => Tile::Wall,
            '.' => Tile::Empty,
            'G' => Tile::Goblin(INITIAL_HITPOINTS),
            'E' => Tile::Elf(INITIAL_HITPOINTS),
            _ => return Err(value),
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Point(CartesianPoint);

impl graph::Point for Point {
    fn neighbours(self) -> impl Iterator<Item = Self>
    where
        Self: Sized,
    {
        let mut result: Vec<_> = self.0.neighbours().map(Point).collect();
        result.sort();
        result.into_iter()
    }
}

impl graph::Cartesian for Point {
    fn from_xy(xy: (usize, usize)) -> Self {
        Self(CartesianPoint::from_xy(xy))
    }

    fn to_xy(&self) -> (usize, usize) {
        self.0.to_xy()
    }
}

impl PartialOrd for Point {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Point {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.0 .1, self.0 .0).cmp(&(other.0 .1, other.0 .0))
    }
}

fn find_units(dungeon: &RectangularWorld<Point, Tile>) -> Vec<(Point, Tile)> {
    let mut result: Vec<_> = dungeon
        .iter()
        .map(|(p, t)| (p, *t))
        .filter(|(_, t)| t.is_unit())
        .collect();
    result.sort();
    result
}

#[cfg(feature = "visualise")]
fn print_dungeon(dungeon: &HashMap<Point, Tile, impl BuildHasher>) {
    let mut result = String::from("---------------------------------------\n");
    for (_, line) in &dungeon
        .iter()
        .sorted()
        .group_by(|(Point(CartesianPoint(_, y)), _)| y)
    {
        for (_, tile) in line {
            result.push(match tile {
                Tile::Wall => '#',
                Tile::Empty => '.',
                Tile::Goblin(_) => 'G',
                Tile::Elf(_) => 'E',
            });
        }
        result.push('\n');
    }
    result.push_str("---------------------------------------");
    println!("{}", result);
}

fn simulate_combat(
    mut dungeon: RectangularWorld<Point, Tile>,
    attack_strength: impl Fn(Tile) -> usize,
) -> (Winner, usize, usize) {
    let mut elf_died = false;
    for round in 0.. {
        #[cfg(feature = "visualise")]
        {
            println!("round {}", round);
            print_dungeon(&dungeon);
        }
        let units = find_units(&dungeon);
        for (mut point, _unit) in &units {
            let unit = dungeon.get(&point).unwrap();
            if !matches!(unit, Tile::Empty) {
                if !dungeon.tiles().any(|tile| unit.is_enemy(tile)) {
                    let remaining_units: Vec<_> =
                        dungeon.tiles().filter(|tile| tile.is_unit()).collect();
                    let winners = match remaining_units[0] {
                        Tile::Goblin(_) => Winner::Goblins,
                        Tile::Elf(_) if elf_died => Winner::ElvesWithLosses,
                        Tile::Elf(_) => Winner::Elves,
                        _ => unreachable!(),
                    };
                    return (
                        winners,
                        round,
                        remaining_units.into_iter().filter_map(Tile::health).sum(),
                    );
                }
                if !point.neighbours().any(|neighbour| {
                    dungeon
                        .get(&neighbour)
                        .map_or(false, |enemy| unit.is_enemy(&enemy))
                }) {
                    if let Some(path) = dungeon
                        .iter()
                        .map(|(p, t)| (p, *t))
                        .filter(|(_, tile)| unit.is_enemy(tile))
                        .flat_map(|(p, _)| dungeon.neighbours(p))
                        .unique()
                        .filter_map(|p| dungeon.path(&point, &p))
                        .min_by_key(|path| (path.len(), path[1]))
                    {
                        let unit = dungeon.insert(point, Tile::Empty).unwrap();
                        point = path[1];
                        assert!(dungeon.insert(point, unit) == Some(Tile::Empty));
                    }
                }
                if let Some(enemy_point) = point
                    .neighbours()
                    .filter(|p| dungeon.get(p).map_or(false, |enemy| unit.is_enemy(&enemy)))
                    .min_by_key(|p| (dungeon.get(p).unwrap().health(), *p))
                {
                    let enemy = dungeon.get_mut(enemy_point).unwrap();
                    let is_elf = matches!(enemy, Tile::Elf(_));
                    enemy.apply_damage(attack_strength(unit)).unwrap();
                    elf_died |= is_elf && matches!(enemy, Tile::Empty);
                }
            }
        }
    }
    unreachable!()
}

fn part_1(dungeon: RectangularWorld<Point, Tile>) -> (usize, usize) {
    let (_winners, turns, remaining_hp) = simulate_combat(dungeon, |_| ATTACK_STRENGTH);
    (turns, remaining_hp)
}

fn part_2(dungeon: RectangularWorld<Point, Tile>) -> (usize, usize, usize) {
    for attack_strength in ATTACK_STRENGTH + 1.. {
        if let (Winner::Elves, turns, remaining_hp) =
            simulate_combat(dungeon.clone(), |tile| match tile {
                Tile::Goblin(_) => ATTACK_STRENGTH,
                Tile::Elf(_) => attack_strength,
                _ => unreachable!(),
            })
        {
            return (attack_strength, turns, remaining_hp);
        }
    }
    unreachable!()
}

#[cfg(test)]
mod tests {
    use graph::{
        ReadExt,
        RectangularWorld,
    };

    use super::{
        part_2,
        simulate_combat,
        Winner,
        ATTACK_STRENGTH,
    };

    #[test]
    fn test_simulate_combat_1() {
        assert!(matches!(
            simulate_combat(RectangularWorld::from_file("input_test_1").unwrap(), |_| {
                ATTACK_STRENGTH
            }),
            (Winner::Goblins, 47, 590)
        ));
    }

    #[test]
    fn test_simulate_combat_2() {
        assert!(matches!(
            simulate_combat(RectangularWorld::from_file("input_test_2").unwrap(), |_| {
                ATTACK_STRENGTH
            }),
            (Winner::Elves | Winner::ElvesWithLosses, 37, 982)
        ));
    }

    #[test]
    fn test_simulate_combat_3() {
        assert!(matches!(
            simulate_combat(RectangularWorld::from_file("input_test_3").unwrap(), |_| {
                ATTACK_STRENGTH
            }),
            (Winner::Elves | Winner::ElvesWithLosses, 46, 859)
        ));
    }

    #[test]
    fn test_simulate_combat_4() {
        assert!(matches!(
            simulate_combat(RectangularWorld::from_file("input_test_4").unwrap(), |_| {
                ATTACK_STRENGTH
            }),
            (Winner::Goblins, 35, 793)
        ));
    }

    #[test]
    fn test_simulate_combat_5() {
        assert!(matches!(
            simulate_combat(RectangularWorld::from_file("input_test_5").unwrap(), |_| {
                ATTACK_STRENGTH
            }),
            (Winner::Goblins, 54, 536)
        ));
    }

    #[test]
    fn test_simulate_combat_6() {
        assert!(matches!(
            simulate_combat(RectangularWorld::from_file("input_test_6").unwrap(), |_| {
                ATTACK_STRENGTH
            }),
            (Winner::Goblins, 20, 937)
        ));
    }

    #[test]
    fn test_part_2_1() {
        assert_eq!(
            part_2(RectangularWorld::from_file("input_test_1").unwrap()),
            (15, 29, 172)
        );
    }

    #[test]
    fn test_part_2_3() {
        assert_eq!(
            part_2(RectangularWorld::from_file("input_test_3").unwrap()),
            (4, 33, 948)
        );
    }

    #[test]
    fn test_part_2_4() {
        assert_eq!(
            part_2(RectangularWorld::from_file("input_test_4").unwrap()),
            (15, 37, 94)
        );
    }

    #[test]
    fn test_part_2_5() {
        assert_eq!(
            part_2(RectangularWorld::from_file("input_test_5").unwrap()),
            (12, 39, 166)
        );
    }

    #[test]
    fn test_part_2_6() {
        assert_eq!(
            part_2(RectangularWorld::from_file("input_test_6").unwrap()),
            (34, 30, 38)
        );
    }
}

fn main() {
    let dungeon = RectangularWorld::from_file("input").unwrap();
    let (turns, remaining_hp) = part_1(dungeon.clone());
    println!("{}", turns * remaining_hp);
    let (_attack_strength, turns, remaining_hp) = part_2(dungeon);
    println!("{}", turns * remaining_hp);
}
