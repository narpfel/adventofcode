#![feature(debug_closure_helpers)]
#![feature(generic_nonzero)]

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
use rustc_hash::FxHashMap;

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
struct State<const WORKER_COUNT: usize> {
    flow: u64,
    workers: [Worker; WORKER_COUNT],
    open_valves: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Worker {
    time_of_arrival: u64,
    location: usize,
}

impl<const WORKER_COUNT: usize> State<WORKER_COUNT> {
    fn is_open(&self, valve: usize) -> bool {
        self.open_valves & (1 << valve) != 0
    }
}

impl<const WORKER_COUNT: usize> PartialOrd for State<WORKER_COUNT> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<const WORKER_COUNT: usize> Ord for State<WORKER_COUNT> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.flow, Reverse(self.workers[0].time_of_arrival))
            .cmp(&(other.flow, Reverse(other.workers[0].time_of_arrival)))
    }
}

impl<const WORKER_COUNT: usize> Debug for State<WORKER_COUNT> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("State")
            .field("flow", &self.flow)
            .field("workers", &self.workers)
            .field_with("open", |f| write!(f, "0b{:064b}", self.open_valves))
            .finish()
    }
}

fn solve<const WORKER_COUNT: usize, const TIME: u64>(
    valves: &[Valve],
    adjacency: &Adjacency,
    start: usize,
) -> u64 {
    let nonzero_valves = valves
        .iter()
        .enumerate()
        .filter(|(_, valve)| valve.flow_rate != 0)
        .map(|(i, valve)| (i, valve.flow_rate))
        .collect::<Vec<_>>();

    let mut seen = FxHashMap::default();
    let mut next = Vec::new();
    next.push(State {
        flow: 0,
        workers: [Worker { time_of_arrival: 0, location: start }; WORKER_COUNT],
        open_valves: 0,
    });

    let all_valves = nonzero_valves.iter().map(|(i, _)| 1 << i).sum::<u64>();

    let mut max_flow = 0;

    while let Some(state) = next.pop() {
        max_flow = max_flow.max(state.flow);

        let Worker { time_of_arrival: time, location } = state.workers[0];
        let remaining_time_open = (|| TIME.checked_sub(time)?.checked_sub(1))().unwrap_or(0);
        let flow_upper_bound = state.flow
            + nonzero_valves
                .iter()
                .filter(|&&(i, _)| !state.is_open(i))
                .map(|(_, flow_rate)| flow_rate * remaining_time_open)
                .sum::<u64>();

        if flow_upper_bound <= max_flow {
            continue;
        }

        let state_id = (state.workers, state.open_valves);
        if !seen.contains_key(&state_id) || seen[&state_id] < flow_upper_bound {
            seen.insert(state_id, flow_upper_bound);

            if time < (TIME - 1) && state.open_valves != all_valves && !state.is_open(location) {
                let one_if_not_start = if location != start { 1 } else { 0 };
                for &(neighbour, distance) in &adjacency[location] {
                    let mut workers = state.workers;
                    workers[0] = Worker {
                        time_of_arrival: time + distance + one_if_not_start,
                        location: neighbour,
                    };
                    workers.sort();
                    next.push(State {
                        flow: state.flow
                            + remaining_time_open * valves[location].flow_rate * one_if_not_start,
                        workers,
                        open_valves: state.open_valves | (one_if_not_start << location),
                    });
                }
            }
        }
    }

    max_flow
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let (valves, adjacency, start) = read_input("input")?;
    println!("{}", solve::<1, 30>(&valves, &adjacency, start));
    println!("{}", solve::<2, 26>(&valves, &adjacency, start));
    Ok(())
}

#[cfg(test)]
mod test {
    use super::read_input;
    use super::solve;

    #[test]
    fn test_part_1() {
        let (valves, adjacency, start) = read_input("input_test").unwrap();
        assert_eq!(solve::<1, 30>(&valves, &adjacency, start), 1651);
    }

    #[test]
    fn test_part_2() {
        let (valves, adjacency, start) = read_input("input_test").unwrap();
        assert_eq!(solve::<2, 26>(&valves, &adjacency, start), 1707);
    }
}
