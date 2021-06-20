use std::{
    cmp::Ordering,
    error::Error,
    io::{
        stdout,
        Write,
    },
};

use itertools::Itertools;

use intcode::{
    Cell,
    Computer,
    IO,
};

type Point = (i64, i64);

struct Tile {
    position: Point,
    tile: Cell,
}

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

struct State {
    outputs: Vec<Cell>,
    tiles: Vec<Tile>,
    paddle_position: i64,
    ball_position: i64,
}

impl State {
    fn new() -> Self {
        State {
            outputs: Vec::new(),
            tiles: Vec::new(),
            paddle_position: 0,
            ball_position: 0,
        }
    }

    fn handle_outputs(&mut self) {
        for (x, y, tile) in std::mem::take(&mut self.outputs).into_iter().tuples() {
            self.tiles.push(Tile { position: (x, y), tile });
            if tile == 3 {
                self.paddle_position = x;
            }
            else if tile == 4 {
                self.ball_position = x;
            }
        }
    }
}

impl IO for State {
    fn next_input(&mut self) -> Option<Cell> {
        self.handle_outputs();
        Some(match self.paddle_position.cmp(&self.ball_position) {
            Ordering::Less => 1,
            Ordering::Equal => 0,
            Ordering::Greater => -1,
        })
    }

    fn output(&mut self, value: Cell) {
        self.outputs.push(value);
    }
}

fn part1() -> Result<usize, Box<dyn Error>> {
    let mut state = State::new();
    let mut c = Computer::from_file("input", &mut state)?;
    c.run().ok_or("error while running program")?;
    state.handle_outputs();
    Ok(state
        .tiles
        .into_iter()
        .filter(|tile| tile.tile == 2)
        .count())
}

fn part2() -> Result<(i64, Vec<Tile>), Box<dyn Error>> {
    let mut state = State::new();
    let mut c = Computer::from_file("input", &mut state)?;
    c.memory[0] = 2;
    c.run().ok_or("error while running program")?;
    state.handle_outputs();
    Ok((
        state
            .tiles
            .iter()
            .rev()
            .filter_map(|&Tile { position, tile }| {
                if position == (-1, 0) {
                    Some(tile)
                }
                else {
                    None
                }
            })
            .next()
            .ok_or("Could not find score in program output")?,
        state.tiles,
    ))
}

fn main() -> Result<(), Box<dyn Error>> {
    let (part2_solution, tiles) = part2()?;

    if std::env::args().nth(1) == Some("--visualise".to_owned()) {
        print!("\x1B[?25l\x1B[2J");
        tiles.iter().for_each(|&Tile { position: (x, y), tile }| {
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
    println!("{}", part2_solution);
    Ok(())
}
