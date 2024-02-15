use std::collections::hash_map::Entry;
use std::io;
use std::path::Path;

use either::Either::Left;
use either::Either::Right;
use fnv::FnvHashMap;

const TOTAL_CYCLE_COUNT: u64 = 1000000000;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Platform {
    round: Vec<Vec<bool>>,
    square: Vec<Vec<bool>>,
}

fn read_input(filename: impl AsRef<Path>) -> io::Result<Platform> {
    let s = std::fs::read_to_string(filename)?;
    let mut round = Vec::new();
    let mut square = Vec::new();
    for line in s.lines() {
        let line = line.trim();
        let mut round_line = vec![false; line.len()];
        let mut square_line = vec![false; line.len()];
        for (i, c) in line.chars().enumerate() {
            match c {
                'O' => round_line[i] = true,
                '#' => square_line[i] = true,
                '.' => (),
                _ => unreachable!("{c:?}"),
            }
        }
        round.push(round_line);
        square.push(square_line);
    }

    Ok(Platform { round, square })
}

fn simulate(platform: &mut Platform, x_offset: isize, y_offset: isize) {
    let x_range = 0..platform.round[0].len();
    let y_range = 0..platform.round.len();

    let x_range_in_iteration_order = if x_offset > 0 {
        Left(x_range.clone().rev())
    }
    else {
        Right(x_range.clone())
    };

    let y_range_in_iteration_order = if y_offset > 0 {
        Left(y_range.clone().rev())
    }
    else {
        Right(y_range.clone())
    };

    for y in y_range_in_iteration_order.clone() {
        for x in x_range_in_iteration_order.clone() {
            let mut x = x;
            let mut y = y;
            if platform.round[y][x] {
                platform.round[y][x] = false;
                loop {
                    x = x.wrapping_add(x_offset as usize);
                    y = y.wrapping_add(y_offset as usize);
                    if !x_range.contains(&x)
                        || !y_range.contains(&y)
                        || platform.round[y][x]
                        || platform.square[y][x]
                    {
                        x = x.wrapping_sub(x_offset as usize);
                        y = y.wrapping_sub(y_offset as usize);
                        break;
                    }
                }
                platform.round[y][x] = true;
            }
        }
    }
}

fn calculate_total_load(platform: &Platform) -> u64 {
    let y_range = 0..platform.round.len();
    platform
        .round
        .iter()
        .enumerate()
        .flat_map(|(i, line)| {
            line.iter()
                .filter_map(move |&is_rock| is_rock.then_some(y_range.end as u64 - i as u64))
        })
        .sum()
}

fn part_1(mut platform: Platform) -> u64 {
    simulate(&mut platform, 0, -1);
    calculate_total_load(&platform)
}

fn part_2(mut platform: Platform) -> u64 {
    let mut seen = FnvHashMap::default();

    for i in 0.. {
        match seen.entry(platform.clone()) {
            Entry::Occupied(_) => {
                let seen_at: FnvHashMap<_, _> = seen
                    .iter()
                    .map(|(platform, time)| (time, platform))
                    .collect();
                let cycle_start = seen[&platform];
                let cycle_length = i - cycle_start;
                let rest = (TOTAL_CYCLE_COUNT - cycle_start) % cycle_length;
                return calculate_total_load(seen_at[&(cycle_start + rest)]);
            }
            Entry::Vacant(entry) => entry.insert(i),
        };

        simulate(&mut platform, 0, -1);
        simulate(&mut platform, -1, 0);
        simulate(&mut platform, 0, 1);
        simulate(&mut platform, 1, 0);
    }
    unreachable!()
}

fn main() -> io::Result<()> {
    let input = read_input("input")?;
    println!("{}", part_1(input.clone()));
    println!("{}", part_2(input.clone()));
    Ok(())
}
