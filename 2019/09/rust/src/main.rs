use std::error::Error;

use intcode::Cell;
use intcode::Computer;

struct Io {
    input: Option<Cell>,
    output: Option<Cell>,
}

impl intcode::IO for Io {
    fn next_input(&mut self) -> Option<Cell> {
        self.input.take()
    }

    fn output(&mut self, value: Cell) {
        self.output = Some(value);
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    for input in [1, 2] {
        let mut io = Io { input: Some(input), output: None };
        let mut computer = Computer::from_file("input", &mut io)?;
        computer.run().unwrap();
        println!("{}", io.output.unwrap());
    }
    Ok(())
}
