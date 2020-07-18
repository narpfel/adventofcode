use std::collections::VecDeque;

const PLAYER_COUNT: u64 = 493;
const HIGHEST_MARBLE_NUMBER: u64 = 71_863;

fn play(player_count: u64, highest_marble_number: u64) -> Option<u64> {
    let mut scores = vec![0; player_count as _];
    let mut marbles = VecDeque::with_capacity(highest_marble_number as usize + 2);
    marbles.push_back(0);
    // Required because `VecDeque` cannot rotate by more than its `len`.
    marbles.push_back(1);
    for (marble, player) in (2..=highest_marble_number).zip((0..player_count).cycle()) {
        if marble % 23 == 0 {
            marbles.rotate_left(7);
            scores[player as usize] += marble + marbles.pop_back()?;
        }
        else {
            marbles.rotate_right(2);
            marbles.push_back(marble);
        }
    }
    scores.into_iter().max()
}

fn main() {
    println!("{}", play(PLAYER_COUNT, HIGHEST_MARBLE_NUMBER).unwrap());
    println!(
        "{}",
        play(PLAYER_COUNT, HIGHEST_MARBLE_NUMBER * 100).unwrap()
    );
}
