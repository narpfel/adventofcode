const INPUT: &[u64] = &[16, 12, 1, 0, 15, 7, 11];

fn solve(starting_numbers: &[u64], turn_count: usize) -> usize {
    let mut number_to_turns: Vec<(i32, i32)> = vec![(-1, -1); turn_count];
    for (i, n) in starting_numbers.iter().enumerate() {
        number_to_turns[*n as usize].0 = i as i32;
    }
    let mut last_spoken = *starting_numbers.last().unwrap() as usize;
    for turn in starting_numbers.len()..turn_count {
        let (x, y) = number_to_turns[last_spoken];
        if y == -1 {
            last_spoken = 0;
        }
        else {
            last_spoken = (x - y) as usize;
        }
        number_to_turns[last_spoken] = (turn as _, number_to_turns[last_spoken].0);
    }
    last_spoken
}

fn main() {
    println!("{}", solve(INPUT, 2020));
    println!("{}", solve(INPUT, 30_000_000));
}
