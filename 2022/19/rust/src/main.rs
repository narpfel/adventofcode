#![feature(once_cell)]

use std::{
    error::Error,
    fs::read_to_string,
    path::Path,
    sync::LazyLock,
};

use rayon::prelude::*;
use regex::Regex;

static BLUEPRINT_RE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(concat!(
        r"Blueprint (?P<id>\d+): ",
        r"Each ore robot costs (?P<ore_robot_ore>\d+) ore. ",
        r"Each clay robot costs (?P<clay_robot_ore>\d+) ore. ",
        r"Each obsidian robot costs (?P<obsidian_robot_ore>\d+) ore ",
        r"and (?P<obsidian_robot_clay>\d+) clay. ",
        r"Each geode robot costs (?P<geode_robot_ore>\d+) ore ",
        r"and (?P<geode_robot_obsidian>\d+) obsidian.",
    ))
    .unwrap()
});

#[derive(Debug, Clone, Copy)]
struct Blueprint {
    id: u64,
    ore_robot: Materials,
    clay_robot: Materials,
    obsidian_robot: Materials,
    geode_robot: Materials,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Materials {
    ore: u64,
    clay: u64,
    obsidian: u64,
    geodes: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Robots {
    ore: u64,
    clay: u64,
    obsidian: u64,
    geodes: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct State {
    time: u64,
    materials: Materials,
    robots: Robots,
}

fn read_input(path: impl AsRef<Path>) -> Result<Vec<Blueprint>, Box<dyn Error>> {
    read_to_string(path)?
        .lines()
        .map(Blueprint::parse)
        .collect()
}

fn max_geodes_impl(bp: &Blueprint, time_limit: u64, state: &State) -> u64 {
    if state.time == time_limit {
        state.materials.geodes
    }
    else {
        let new_state = state.step();
        if state.can_afford(&bp.geode_robot) {
            max_geodes_impl(
                bp,
                time_limit,
                &new_state.build_geode_robot(&bp.geode_robot),
            )
        }
        else {
            let mut max_geodes = max_geodes_impl(bp, time_limit, &new_state);
            if state.can_afford(&bp.obsidian_robot) {
                max_geodes = max_geodes.max(max_geodes_impl(
                    bp,
                    time_limit,
                    &new_state.build_obsidian_robot(&bp.obsidian_robot),
                ));
            }
            if state.can_afford(&bp.ore_robot) {
                max_geodes = max_geodes.max(max_geodes_impl(
                    bp,
                    time_limit,
                    &new_state.build_ore_robot(&bp.ore_robot),
                ));
            }
            if state.can_afford(&bp.clay_robot) {
                max_geodes = max_geodes.max(max_geodes_impl(
                    bp,
                    time_limit,
                    &new_state.build_clay_robot(&bp.clay_robot),
                ));
            }
            max_geodes
        }
    }
}

impl Blueprint {
    fn parse(line: &str) -> Result<Self, Box<dyn Error>> {
        let blueprint_re = LazyLock::force(&BLUEPRINT_RE);
        let captures = blueprint_re.captures(line).ok_or("no match")?;
        Ok(Self {
            id: captures["id"].parse()?,
            ore_robot: Materials {
                ore: captures["ore_robot_ore"].parse()?,
                ..Materials::default()
            },
            clay_robot: Materials {
                ore: captures["clay_robot_ore"].parse()?,
                ..Materials::default()
            },
            obsidian_robot: Materials {
                ore: captures["obsidian_robot_ore"].parse()?,
                clay: captures["obsidian_robot_clay"].parse()?,
                ..Materials::default()
            },
            geode_robot: Materials {
                ore: captures["geode_robot_ore"].parse()?,
                obsidian: captures["geode_robot_obsidian"].parse()?,
                ..Materials::default()
            },
        })
    }

    fn max_geodes(&self, time_limit: u64) -> u64 {
        max_geodes_impl(
            self,
            time_limit,
            &State {
                time: 0,
                materials: Materials::default(),
                robots: Robots { ore: 1, clay: 0, obsidian: 0, geodes: 0 },
            },
        )
    }

    fn quality_level(&self) -> u64 {
        self.max_geodes(24) * self.id
    }
}

impl Materials {
    fn can_afford(&self, other: &Self) -> bool {
        self.ore >= other.ore
            && self.clay >= other.clay
            && self.obsidian >= other.obsidian
            && !(self.ore >= 2 * other.ore
                && self.clay >= 2 * other.clay
                && self.obsidian >= 2 * other.obsidian)
    }

    fn spend(&self, other: &Self) -> Self {
        Self {
            ore: self.ore - other.ore,
            clay: self.clay - other.clay,
            obsidian: self.obsidian - other.obsidian,
            geodes: self.geodes - other.geodes,
        }
    }
}

impl State {
    fn step(&self) -> Self {
        Self {
            time: self.time + 1,
            materials: Materials {
                ore: self.materials.ore + self.robots.ore,
                clay: self.materials.clay + self.robots.clay,
                obsidian: self.materials.obsidian + self.robots.obsidian,
                geodes: self.materials.geodes + self.robots.geodes,
            },
            robots: self.robots,
        }
    }

    fn can_afford(&self, cost: &Materials) -> bool {
        self.materials.can_afford(cost)
            && !(cost.ore + self.robots.ore <= self.materials.ore
                && cost.clay + self.robots.clay <= self.materials.clay
                && cost.obsidian + self.robots.obsidian <= self.materials.obsidian)
    }

    fn build_ore_robot(&self, cost: &Materials) -> Self {
        Self {
            time: self.time,
            materials: self.materials.spend(cost),
            robots: Robots { ore: self.robots.ore + 1, ..self.robots },
        }
    }

    fn build_clay_robot(&self, cost: &Materials) -> Self {
        Self {
            time: self.time,
            materials: self.materials.spend(cost),
            robots: Robots {
                clay: self.robots.clay + 1,
                ..self.robots
            },
        }
    }

    fn build_obsidian_robot(&self, cost: &Materials) -> Self {
        Self {
            time: self.time,
            materials: self.materials.spend(cost),
            robots: Robots {
                obsidian: self.robots.obsidian + 1,
                ..self.robots
            },
        }
    }

    fn build_geode_robot(&self, cost: &Materials) -> Self {
        Self {
            time: self.time,
            materials: self.materials.spend(cost),
            robots: Robots {
                geodes: self.robots.geodes + 1,
                ..self.robots
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_part_1() {
        let blueprints = read_input("input_test").unwrap();
        assert_eq!(blueprints[0].quality_level(), 9);
        assert_eq!(blueprints[1].quality_level(), 24);
    }

    #[test]
    fn test_part_2() {
        let blueprints = read_input("input_test").unwrap();
        assert_eq!(blueprints[0].max_geodes(32), 56);
        assert_eq!(blueprints[1].max_geodes(32), 62);
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let blueprints = read_input("input")?;
    let (part_1, part_2) = rayon::join(
        || blueprints.iter().map(Blueprint::quality_level).sum::<u64>(),
        || {
            blueprints
                .par_iter()
                .take(3)
                .map(|blueprint| blueprint.max_geodes(32))
                .product::<u64>()
        },
    );
    println!("{part_1}");
    println!("{part_2}");
    Ok(())
}
