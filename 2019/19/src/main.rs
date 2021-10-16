use std::error::Error;

use intcode::read_puzzle_input;
use intcode::Cell;
use intcode::Computer;
use intcode::Memory;
use intcode::IO;
use itertools::Itertools;

const SIZE: usize = 100;

struct State {
    x: Option<Cell>,
    y: Option<Cell>,
    result: Option<Cell>,
}

impl IO for State {
    fn next_input(&mut self) -> Option<Cell> {
        self.x.take().or_else(|| self.y.take())
    }

    fn output(&mut self, value: Cell) {
        self.result = Some(value);
    }
}

fn is_tile_covered(#[allow(clippy::ptr_arg)] memory: &Memory, x: usize, y: usize) -> bool {
    let mut state = State {
        x: Some(x as _),
        y: Some(y as _),
        result: None,
    };
    let mut computer = Computer::new(memory.clone(), &mut state);
    computer.run();
    state.result == Some(1)
}

fn part_2(memory: Memory) -> u64 {
    let mut y = 0;
    for x in 0.. {
        if !is_tile_covered(&memory, x, y) {
            y += 1;
        }

        while is_tile_covered(&memory, x, y + 1) {
            y += 1;
            if let Some(y2) = y.checked_sub(SIZE - 1) {
                let x2 = x + SIZE - 1;
                // This assumes the tractor beam is convex
                if is_tile_covered(&memory, x2, y)
                    && is_tile_covered(&memory, x, y2)
                    && is_tile_covered(&memory, x2, y2)
                {
                    return 10_000 * x as u64 + y2 as u64;
                }
            }
        }
    }
    unreachable!()
}

fn main() -> Result<(), Box<dyn Error>> {
    let code = read_puzzle_input("input")?;
    let part_1 = (0..50)
        .cartesian_product(0..50)
        .filter(|(x, y)| is_tile_covered(&code, *x, *y))
        .count();
    println!("{}", part_1);
    println!("{}", part_2(code));
    Ok(())
}
