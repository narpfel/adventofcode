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

fn part_2(position_1: u64, position_2: u64, score_1: u64, score_2: u64) -> [u64; 2] {
    let mut wins_1 = 0;
    let mut wins_2 = 0;
    for &(roll, multiplicity) in &DICE {
        let position = (position_1 + roll as u64) % 10;
        let score = score_1 + position + 1;
        if score >= 21 {
            wins_1 += multiplicity;
        }
        else {
            let [w2, w1] = part_2(position_2, position, score_2, score);
            wins_1 += w1 * multiplicity;
            wins_2 += w2 * multiplicity;
        }
    }
    [wins_1, wins_2]
}

fn main() {
    let players = [
        Player::new(0, STARTING_POSITIONS.0),
        Player::new(1, STARTING_POSITIONS.1),
    ];
    println!("{}", part_1(players));
    let win_counts = part_2(
        STARTING_POSITIONS.0 as u64 - 1,
        STARTING_POSITIONS.1 as u64 - 1,
        0,
        0,
    );
    println!("{}", win_counts.into_iter().max().unwrap());
}
