use std::collections::HashMap;
use std::sync::mpsc::channel;
use std::iter::{once, from_fn};
use std::convert::TryInto;

use failure::{Fallible, ensure};

use intcode::Computer;


#[derive(Debug, Copy, Clone)]
enum Direction {
    Up, Down, Left, Right
}
use Direction::*;

#[derive(Debug, Copy, Clone)]
enum Colour {
    Black, White
}
use Colour::*;

fn next_direction(direction: Direction, turn: i64) -> Option<Direction> {
    match (direction, turn) {
        (Up, 0) => Some(Left),
        (Up, 1) => Some(Right),
        (Down, 0) => Some(Right),
        (Down, 1) => Some(Left),
        (Left, 0) => Some(Down),
        (Left, 1) => Some(Up),
        (Right, 0) => Some(Up),
        (Right, 1) => Some(Down),
        _ => None,
    }
}

fn move_((mut x, mut y): (i64, i64), direction: Direction) -> (i64, i64) {
    match direction {
        Up => y += 1,
        Down => y -= 1,
        Left => x -= 1,
        Right => x += 1,
    };
    (x, y)
}

fn solve(tiles: &mut HashMap<(i64, i64), Colour>) -> Fallible<()> {
    let mut position = (0, 0);
    macro_rules! lookup_colour {
        () => {{
            tiles.get(&position).map(|colour| match colour { Black => 0, White => 1 }).unwrap_or(0)
        }}
    }
    let (tx, rx) = channel();
    let mut direction = Direction::Up;
    let robot = once(lookup_colour!()).chain(from_fn(|| {
        let colour = rx.recv().ok()?;
        let turn = rx.recv().ok()?;
        tiles.insert(position, match colour {
            0 => Black,
            1 => White,
            _ => None?,
        });
        direction = next_direction(direction, turn)?;
        position = move_(position, direction);
        Some(lookup_colour!())
    }));

    let mut c = Computer::from_file("input", robot, tx)?;
    ensure!(c.run().is_some(), "error while executing program");
    Ok(())
}

fn part1() -> Fallible<usize> {
    let mut tiles = HashMap::new();
    solve(&mut tiles)?;
    Ok(tiles.len())
}

fn part2() -> Fallible<String> {
    let mut tiles = HashMap::new();
    tiles.insert((0, 0), White);
    solve(&mut tiles)?;

    let (min_x, min_y) =
        tiles.keys().fold((1, 0), |(min_x, min_y), (x, y)| (*x.min(&min_x), *y.min(&min_y)));
    let mut lines: Vec<Vec<char>> = Vec::new();
    for ((x, y), ref colour) in tiles {
        if y - min_y >= lines.len() as i64 {
            lines.resize((y - min_y + 1).try_into()?, Vec::new());
        }
        let line = &mut lines[(y - min_y) as usize];
        if x - min_x >= line.len() as i64 {
            line.resize((x - min_x + 1).try_into()?, ' ');
        }
        line[(x - min_x) as usize] = match colour { White => '#', Black => ' ' };
    }
    Ok(lines.iter().rev().map(|line| line.iter().collect()).collect::<Vec<String>>().join("\n"))
}

fn main() -> Fallible<()> {
    println!("{}", part1()?);
    println!("{}", part2()?);
    Ok(())
}
