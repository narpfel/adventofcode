const INPUT: &[u64] = &[16, 12, 1, 0, 15, 7, 11];

fn solve(starting_numbers: &[u64], turn_count: usize) -> usize {
    let mut number_to_turn = vec![-1_i32; turn_count];
    for (i, n) in starting_numbers
        .iter()
        .take(starting_numbers.len() - 1)
        .enumerate()
    {
        number_to_turn[*n as usize] = i as _;
    }
    let mut last_spoken = *starting_numbers.last().unwrap() as usize;
    for turn in starting_numbers.len()..turn_count {
        let last_spoken_on_turn = number_to_turn[last_spoken];
        number_to_turn[last_spoken] = (turn - 1) as _;
        if last_spoken_on_turn == -1 {
            last_spoken = 0;
        }
        else {
            last_spoken = turn - last_spoken_on_turn as usize - 1;
        }
    }
    last_spoken
}

fn main() {
    println!("{}", solve(INPUT, 2020));
    println!("{}", solve(INPUT, 30_000_000));
}
