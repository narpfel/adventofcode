use std::{
    collections::HashSet,
    error::Error,
    iter::repeat,
};

use itertools::Itertools;

use intcode::{
    read_puzzle_input,
    Cell,
    Computer,
    Memory,
    IO,
};

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

fn is_tile_covered(memory: Memory, x: usize, y: usize) -> bool {
    let mut state = State {
        x: Some(x as _),
        y: Some(y as _),
        result: None,
    };
    let mut computer = Computer::new(memory, &mut state);
    computer.run();
    state.result == Some(1)
}

fn part_2(memory: Memory) -> u64 {
    let mut covered_tiles = HashSet::new();
    // TODO: Walking the upper and lower edges of the tractor beam is sufficient.
    // This makes the solution linear in `SIZE` instead of quadratic.
    for i in 0.. {
        for (x, y) in repeat(i).zip(0..=i).chain((0..=i).zip(repeat(i))) {
            if is_tile_covered(memory.clone(), x, y) {
                covered_tiles.insert((x, y));
                if let Some((x2, y2)) = x.checked_sub(SIZE - 1).zip(y.checked_sub(SIZE - 1)) {
                    // This assumes the tractor beam is convex
                    if covered_tiles.contains(&(x2, y))
                        && covered_tiles.contains(&(x, y2))
                        && covered_tiles.contains(&(x2, y2))
                    {
                        return 10_000 * x2 as u64 + y2 as u64;
                    }
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
        .filter(|(x, y)| is_tile_covered(code.clone(), *x, *y))
        .count();
    println!("{}", part_1);
    println!("{}", part_2(code));
    Ok(())
}
