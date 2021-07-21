use std::error::Error;

use itertools::Itertools;

use intcode::{
    read_puzzle_input,
    Cell,
    Computer,
    IO,
};

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

fn main() -> Result<(), Box<dyn Error>> {
    let code = read_puzzle_input("input")?;
    let part_1 = (0..50)
        .cartesian_product(0..50)
        .filter(|(x, y)| {
            let mut state = State { x: Some(*x), y: Some(*y), result: None };
            let mut computer = Computer::new(code.clone(), &mut state);
            computer.run();
            state.result == Some(1)
        })
        .count();
    println!("{}", part_1);
    Ok(())
}
