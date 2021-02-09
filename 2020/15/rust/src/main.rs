use std::collections::HashMap;

const INPUT: &[u64] = &[16, 12, 1, 0, 15, 7, 11];

fn solve(starting_numbers: &[u64], turn_count: usize) -> u64 {
    let mut number_to_turns: HashMap<u64, Vec<u64>> = starting_numbers
        .iter()
        .enumerate()
        .map(|(i, &n)| (n, vec![i as u64]))
        .collect();
    let mut last_spoken = *starting_numbers.last().unwrap();
    for turn in starting_numbers.len()..turn_count {
        let spoken_on = number_to_turns.entry(last_spoken).or_insert_with(Vec::new);
        if spoken_on.len() == 1 {
            last_spoken = 0;
        }
        else {
            last_spoken = spoken_on.last().unwrap() - spoken_on.iter().nth_back(1).unwrap();
        }
        number_to_turns
            .entry(last_spoken)
            .or_insert_with(Vec::new)
            .push(turn as u64);
    }
    last_spoken
}

fn main() {
    println!("{}", solve(INPUT, 2020));
    println!("{}", solve(INPUT, 30_000_000));
}
