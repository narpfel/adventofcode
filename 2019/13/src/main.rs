use std::cmp::Ordering;
use std::io::{Write, stdout};
use std::iter::from_fn;
use std::sync::mpsc::channel;

use failure::{Fallible, ensure};
use itertools::Itertools;

use intcode::Computer;

fn render(tile: i64) -> char {
    match tile {
        0 => ' ',
        1 => '\u{2588}',
        2 => '\u{25A0}',
        3 => '_',
        4 => '●',
        _ => unreachable!(),
    }
}

fn part1() -> Fallible<usize> {
    let (tx, rx) = channel();
    let mut c = Computer::from_file("input", vec![].into_iter(), tx)?;
    ensure!(c.run().is_some(), "error while running program");
    Ok(rx.try_iter()
        .tuples()
        .filter(|&(_, _, tile)| tile == 2)
        .count())
}

fn main() -> Fallible<()> {
    let (tx, rx) = channel();
    let mut outputs = Vec::new();

    let mut paddle_position = 0;
    let mut ball_position = 0;
    let input_iterator = from_fn(|| {
        for (x, y, tile) in rx.try_iter().tuples() {
            outputs.push(((x, y), tile));
            if tile == 3 {
                paddle_position = x;
            }
            else if tile == 4 {
                ball_position = x;
            }
        }
        match paddle_position.cmp(&ball_position) {
            Ordering::Less => Some(1),
            Ordering::Equal => Some(0),
            Ordering::Greater => Some(-1),
        }
    });

    let mut c = Computer::from_file("input", input_iterator, tx)?;
    c.memory[0] = 2;
    ensure!(c.run().is_some(), "error while running program");

    outputs.extend(rx.try_iter().tuples().map(|(x, y, tile)| ((x, y), tile)));

    if std::env::args().nth(1) == Some("--visualise".to_owned()) {
        print!("\x1B[?25l\x1B[2J");
        outputs.iter()
            .for_each(|&((x, y), tile)| {
                if x == -1 && y == 0 {
                    print!("\x1B[H{}", tile);
                }
                else {
                    print!("\x1B[{};{}H{}", y + 2, x + 1, render(tile));
                }
                stdout().flush().unwrap();
                std::thread::sleep(std::time::Duration::from_millis(10));
            });
        print!("\x1B[?25h\x1B[30E");
    }

    println!("{}", part1()?);
    println!(
        "{}",
        outputs.iter().rev()
        .filter_map(|&((x, y), tile)| if (x, y) == (-1, 0) { Some(tile) } else { None })
        .next().unwrap()
    );
    Ok(())
}
