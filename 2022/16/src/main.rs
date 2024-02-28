#![feature(generic_nonzero)]
#![feature(debug_closure_helpers)]

use std::cmp::min;
use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Debug;
use std::fs::File;
use std::io::BufRead;
use std::io::BufReader;
use std::num::NonZero;
use std::path::Path;

use regex::Regex;

#[derive(Debug, Clone)]
struct Valve {
    name: String,
    flow_rate: u64,
    connections: Vec<String>,
}

type Adjacency = Vec<Vec<(usize, u64)>>;

fn read_input(
    filename: impl AsRef<Path>,
) -> Result<(Vec<Valve>, Adjacency, usize), Box<dyn std::error::Error>> {
    let valve_re = Regex::new(concat!(
        r"Valve (?P<valve>..) has flow rate=(?P<flow_rate>\d+); ",
        r"tunnels? leads? to valves? (?P<valves>.*)",
    ))
    .unwrap();

    let input = File::open(filename)?;
    let input = BufReader::new(input);

    let valves = input
        .lines()
        .map(|line| {
            let line = line?;
            let captures = valve_re.captures(&line).unwrap();

            Ok::<_, Box<dyn std::error::Error>>(Valve {
                name: captures["valve"].to_owned(),
                flow_rate: captures["flow_rate"].parse()?,
                connections: captures["valves"]
                    .split(", ")
                    .map(ToOwned::to_owned)
                    .collect(),
            })
        })
        .collect::<Result<Vec<_>, _>>()?;

    let name_to_index = valves
        .iter()
        .enumerate()
        .map(|(i, valve)| (&*valve.name, i))
        .collect();
    let adjacency = valves
        .iter()
        .map(|start| compute_distances(&valves, &name_to_index, start))
        .collect();

    let start = name_to_index["AA"];
    Ok((valves, adjacency, start))
}

fn compute_distances(
    valves: &[Valve],
    name_to_index: &HashMap<&str, usize>,
    start: &Valve,
) -> Vec<(usize, u64)> {
    let mut seen = HashSet::new();
    let mut next_valves = BinaryHeap::new();
    let start_name = name_to_index[&*start.name];
    next_valves.push((Reverse(0_u64), start_name));
    let mut result = vec![None; valves.len()];

    while let Some((Reverse(distance), index)) = next_valves.pop() {
        if !seen.contains(&index) {
            seen.insert(index);
            let valve = &valves[index];
            if valve.flow_rate != 0 && index != start_name {
                result[index] = Some(NonZero::new(distance).unwrap());
            }
            for name in valve.connections.iter() {
                next_valves.push((Reverse(distance + 1), name_to_index[&**name]));
            }
        }
    }
    result
        .iter()
        .enumerate()
        .filter_map(|(i, &distance)| Some((i, distance?.get())))
        .collect()
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct State {
    flow: u64,
    time: u64,
    location_1: usize,
    time_1: u64,
    location_2: usize,
    time_2: u64,
    open_valves: u64,
}

impl State {
    fn is_open(&self, valve: usize) -> bool {
        self.open_valves & (1 << valve) != 0
    }
}

impl PartialOrd for State {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for State {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.flow, Reverse(self.time)).cmp(&(other.flow, Reverse(other.time)))
    }
}

impl Debug for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("State")
            .field("flow", &self.flow)
            .field("time", &self.time)
            .field("loc1", &self.location_1)
            .field("t1", &self.time_1)
            .field("loc2", &self.location_2)
            .field("t2", &self.time_2)
            .field_with("open", |f| write!(f, "0b{:064b}", self.open_valves))
            .finish()
    }
}

fn part_1(valves: &[Valve], adjacency: &Adjacency, start: usize) -> u64 {
    let mut seen = HashMap::new();
    let mut next = BinaryHeap::new();
    next.push(State {
        flow: 0,
        time: 0,
        location_1: start,
        time_1: 0,
        location_2: 0,
        time_2: 0,
        open_valves: 0,
    });

    let all_valves = valves
        .iter()
        .enumerate()
        .map(|(i, valve)| {
            if valve.flow_rate == 0 {
                0
            }
            else {
                1 << i
            }
        })
        .sum::<u64>();

    let mut max_flow = 0;

    while let Some(state) = next.pop() {
        let state_id = (state.location_1, state.open_valves);
        if !seen.contains_key(&state_id) || seen[&state_id] < state.flow {
            seen.insert(state_id, state.flow);
            if state.time >= 29 || state.open_valves == all_valves {
                max_flow = max_flow.max(state.flow);
            }
            else {
                for &(neighbour, distance) in &adjacency[state.location_1] {
                    if !state.is_open(neighbour) {
                        let time_open = (|| {
                            30_u64
                                .checked_sub(state.time)?
                                .checked_sub(distance)?
                                .checked_sub(1)
                        })()
                        .unwrap_or(0);
                        next.push(State {
                            flow: state.flow + time_open * valves[neighbour].flow_rate,
                            time: state.time + distance + 1,
                            location_1: neighbour,
                            time_1: 0,
                            location_2: 0,
                            time_2: 0,
                            open_valves: state.open_valves | (1 << neighbour),
                        });
                    }
                }
            }
        }
    }

    max_flow
}

fn part_2(valves: &[Valve], adjacency: &Adjacency, start: usize) -> u64 {
    let mut seen = HashMap::new();
    let mut next = BinaryHeap::new();
    next.push(State {
        flow: 0,
        time: 0,
        location_1: start,
        time_1: 0,
        location_2: start,
        time_2: 0,
        open_valves: 0,
    });

    let all_valves = valves
        .iter()
        .enumerate()
        .map(|(i, valve)| {
            if valve.flow_rate == 0 {
                0
            }
            else {
                1 << i
            }
        })
        .sum::<u64>();

    let mut max_flow = 0;

    while let Some(state) = next.pop() {
        let remaining_time_open =
            (|| 26_u64.checked_sub(state.time)?.checked_sub(1))().unwrap_or(0);
        let flow_upper_bound = state.flow
            + valves
                .iter()
                .enumerate()
                .filter(|&(i, _)| !state.is_open(i))
                .map(|(_, valve)| valve.flow_rate * remaining_time_open)
                .sum::<u64>();

        if flow_upper_bound <= max_flow {
            continue;
        }

        let state_id = (state.location_1, state.location_2, state.open_valves);
        if !seen.contains_key(&state_id) || seen[&state_id] < flow_upper_bound {
            seen.insert(state_id, flow_upper_bound);

            if state.time >= 25 || state.open_valves == all_valves {
                max_flow = max_flow.max(state.flow);
            }
            else if state.time_1 == state.time && state.time_2 == state.time {
                if state.location_1 == start && state.location_2 == start {
                    for &(neighbour_1, distance_1) in &adjacency[state.location_1] {
                        for &(neighbour_2, distance_2) in &adjacency[state.location_2] {
                            let next_time = min(state.time + distance_1, state.time + distance_2);
                            if next_time <= 26
                                && !state.is_open(neighbour_1)
                                && !state.is_open(neighbour_2)
                            {
                                next.push(State {
                                    flow: state.flow,
                                    time: next_time,
                                    location_1: neighbour_1,
                                    time_1: state.time + distance_1,
                                    location_2: neighbour_2,
                                    time_2: state.time + distance_2,
                                    open_valves: state.open_valves,
                                });
                            }
                        }
                    }
                }
                else if !state.is_open(state.location_1) && state.is_open(state.location_2) {
                    for &(neighbour_1, distance_1) in &adjacency[state.location_1] {
                        for &(neighbour_2, distance_2) in &adjacency[state.location_2] {
                            let next_time =
                                min(state.time + distance_1 + 1, state.time + distance_2);
                            if next_time <= 26
                                && !state.is_open(neighbour_1)
                                && !state.is_open(neighbour_2)
                            {
                                next.push(State {
                                    flow: state.flow
                                        + remaining_time_open * valves[state.location_1].flow_rate,
                                    time: next_time,
                                    location_1: neighbour_1,
                                    time_1: state.time + distance_1 + 1,
                                    location_2: neighbour_2,
                                    time_2: state.time + distance_2,
                                    open_valves: state.open_valves | (1 << state.location_1),
                                });
                            }
                        }
                    }
                }
                else if state.is_open(state.location_1) && !state.is_open(state.location_2) {
                    for &(neighbour_1, distance_1) in &adjacency[state.location_1] {
                        for &(neighbour_2, distance_2) in &adjacency[state.location_2] {
                            let next_time =
                                min(state.time + distance_1, state.time + distance_2 + 1);
                            if next_time <= 26
                                && !state.is_open(neighbour_1)
                                && !state.is_open(neighbour_2)
                            {
                                next.push(State {
                                    flow: state.flow
                                        + remaining_time_open * valves[state.location_2].flow_rate,
                                    time: next_time,
                                    location_1: neighbour_1,
                                    time_1: state.time + distance_1,
                                    location_2: neighbour_2,
                                    time_2: state.time + distance_2 + 1,
                                    open_valves: state.open_valves | (1 << state.location_2),
                                });
                            }
                        }
                    }
                }
                else if state.location_1 != state.location_2
                    && !state.is_open(state.location_1)
                    && !state.is_open(state.location_2)
                {
                    for &(neighbour_1, distance_1) in &adjacency[state.location_1] {
                        for &(neighbour_2, distance_2) in &adjacency[state.location_2] {
                            let next_time =
                                min(state.time + distance_1 + 1, state.time + distance_2 + 1);
                            if next_time <= 26
                                && !state.is_open(neighbour_1)
                                && !state.is_open(neighbour_2)
                            {
                                next.push(State {
                                    flow: state.flow
                                        + remaining_time_open
                                            * (valves[state.location_1].flow_rate
                                                + valves[state.location_2].flow_rate),
                                    time: next_time,
                                    location_1: neighbour_1,
                                    time_1: state.time + distance_1 + 1,
                                    location_2: neighbour_2,
                                    time_2: state.time + distance_2 + 1,
                                    open_valves: state.open_valves
                                        | (1 << state.location_1)
                                        | (1 << state.location_2),
                                });
                            }
                        }
                    }
                }
            }
            else if state.time_1 == state.time && !state.is_open(state.location_1) {
                for &(neighbour_1, distance_1) in &adjacency[state.location_1] {
                    let next_time = min(state.time + distance_1 + 1, state.time_2);
                    if next_time <= 26 && !state.is_open(neighbour_1) {
                        next.push(State {
                            flow: state.flow
                                + remaining_time_open * valves[state.location_1].flow_rate,
                            time: next_time,
                            location_1: neighbour_1,
                            time_1: state.time + distance_1 + 1,
                            location_2: state.location_2,
                            time_2: state.time_2,
                            open_valves: state.open_valves | (1 << state.location_1),
                        });
                    }
                }
            }
            else if state.time_2 == state.time && !state.is_open(state.location_2) {
                for &(neighbour_2, distance_2) in &adjacency[state.location_2] {
                    let next_time = min(state.time_1, state.time + distance_2 + 1);
                    if next_time <= 26 && !state.is_open(neighbour_2) {
                        next.push(State {
                            flow: state.flow
                                + remaining_time_open * valves[state.location_2].flow_rate,
                            time: next_time,
                            location_1: state.location_1,
                            time_1: state.time_1,
                            location_2: neighbour_2,
                            time_2: state.time + distance_2 + 1,
                            open_valves: state.open_valves | (1 << state.location_2),
                        });
                    }
                }
            }
            else if ![state.time_1, state.time_2].contains(&state.time) {
                unreachable!()
            }
        }
    }

    max_flow
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let (valves, adjacency, start) = read_input("input")?;
    println!("{}", part_1(&valves, &adjacency, start));
    println!("{}", part_2(&valves, &adjacency, start));
    Ok(())
}

#[cfg(test)]
mod test {
    use super::part_1;
    use super::part_2;
    use super::read_input;

    #[test]
    fn test_part_1() {
        let (valves, adjacency, start) = read_input("input_test").unwrap();
        assert_eq!(part_1(&valves, &adjacency, start), 1651);
    }

    #[test]
    fn test_part_2() {
        let (valves, adjacency, start) = read_input("input_test").unwrap();
        // FIXME: part 2 is not correct, as it prunes states too aggressively. However, it works
        // for the real input.
        assert_eq!(part_2(&valves, &adjacency, start), 1707);
    }
}
