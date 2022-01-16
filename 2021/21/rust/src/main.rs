use std::iter::from_fn;

const STARTING_POSITIONS: (u8, u8) = (3, 10);
const DICE: [(u8, u64); 7] = [(3, 1), (4, 3), (5, 6), (6, 7), (7, 6), (8, 3), (9, 1)];

#[derive(Copy, Clone)]
struct Player {
    name: u8,
    position: u8,
    score: u64,
}

impl Player {
    fn new(name: u8, position: u8) -> Self {
        Self { name, position: position - 1, score: 0 }
    }

    fn roll(&mut self, roll: u64) {
        self.position = ((self.position as u64 + roll) % 10) as _;
        self.score += self.position as u64 + 1;
    }
}

fn swap<T: Copy>(ts: [T; 2]) -> [T; 2] {
    [ts[1], ts[0]]
}

fn part_1(mut players: [Player; 2]) -> u64 {
    let mut die = (1..=100).cycle();
    let rolls = from_fn(|| Some(die.next()? + die.next()? + die.next()?));
    for (i, roll) in rolls.enumerate() {
        let player = &mut players[i % 2];
        player.roll(roll);
        if player.score >= 1000 {
            return (i as u64 + 1) * 3 * players[(player.name as usize + 1) % 2].score;
        }
    }
    unreachable!()
}

fn part_2(players: [Player; 2], universe_count: u64) -> [u64; 2] {
    let mut result = [0, 0];
    for &(roll, multiplicity) in &DICE {
        let mut players = players;
        let player = &mut players[0];
        player.roll(roll as _);
        if player.score >= 21 {
            result[player.name as usize] += universe_count * multiplicity;
        }
        else {
            let results = part_2(swap(players), universe_count * multiplicity);
            result[0] += results[0];
            result[1] += results[1];
        }
    }
    result
}

fn main() {
    let players = [
        Player::new(0, STARTING_POSITIONS.0),
        Player::new(1, STARTING_POSITIONS.1),
    ];
    println!("{}", part_1(players));
    let win_counts = part_2(players, 1);
    println!("{}", win_counts.into_iter().max().unwrap());
}
