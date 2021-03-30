#![feature(bindings_after_at)]
use std::{
    collections::VecDeque,
    iter::from_fn,
};

use itertools::Itertools;

use md5::{
    format_digest,
    md5,
};

#[repr(u8)]
enum Direction {
    Up = b'U',
    Down = b'D',
    Left = b'L',
    Right = b'R',
}
use Direction::*;

#[derive(Default, Debug, Copy, Clone, Eq, PartialEq)]
struct Position(i32, i32);

impl Position {
    fn neighbours(self) -> impl Iterator<Item = (Position, Direction, bool)> {
        let Position(x, y) = self;
        vec![
            (Position(x, y - 1), Up),
            (Position(x, y + 1), Down),
            (Position(x - 1, y), Left),
            (Position(x + 1, y), Right),
        ]
        .into_iter()
        .map(|(p @ Position(x, y), direction)| {
            (p, direction, ((0..=3).contains(&x) && (0..=3).contains(&y)))
        })
    }
}

const INPUT: &str = "rrrbmfta";

fn is_open(input: &str, path: &str) -> [bool; 4] {
    let mut s = input.to_owned();
    s.push_str(path);
    let digest = format_digest(md5(s.as_bytes()));
    let o = |c| (b'b'..=b'f').contains(&c);
    [o(digest[0]), o(digest[1]), o(digest[2]), o(digest[3])]
}

fn iter_paths(input: &str) -> impl Iterator<Item = String> + '_ {
    let mut queue = VecDeque::new();
    queue.push_back((Position(0, 0), String::new()));
    from_fn(move || {
        let (position, path) = queue.pop_front()?;
        if position == Position(3, 3) {
            return Some(Some(path));
        }
        for ((neighbour, direction, reachable), &open) in
            position.neighbours().zip(is_open(input, &path).iter())
        {
            if reachable && open {
                let mut path = path.clone();
                path.push(direction as u8 as char);
                queue.push_back((neighbour, path));
            }
        }
        Some(None)
    })
    .flatten()
}

fn solve(input: &str) -> Option<(String, usize)> {
    iter_paths(input)
        .minmax_by_key(String::len)
        .into_option()
        .map(|(shortest, longest)| (shortest, longest.len()))
}

#[cfg(test)]
mod tests {
    use super::solve;

    #[test]
    fn test() {
        let inputs = ["ihgpwlah", "kglvqrro", "ulqzkmiv"];
        let expected = [
            Some(("DDRRRD".into(), 370)),
            Some(("DDUDRLRRUDRD".into(), 492)),
            Some(("DRURDRUDDLLDLUURRDULRLDUUDDDRR".into(), 830)),
        ];
        for (input, expected) in inputs.iter().zip(expected.iter()) {
            assert_eq!(&solve(input), expected);
        }
    }
}

fn main() {
    let (shortest_path, maximum_path_length) = solve(INPUT).unwrap();
    println!("{}", shortest_path);
    println!("{}", maximum_path_length);
}
