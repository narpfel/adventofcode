use std::{
    collections::VecDeque,
    error::Error,
    fs::read_to_string,
    io::stdin,
};

use intcode::{
    Cell,
    Computer,
};

struct State {
    input: VecDeque<Cell>,
}

impl intcode::IO for State {
    fn next_input(&mut self) -> Option<Cell> {
        if self.input.is_empty() {
            let mut line = String::new();
            stdin().read_line(&mut line).unwrap();
            self.input.extend(line.bytes().map(Cell::from));
        }
        self.input.pop_front()
    }

    fn output(&mut self, value: Cell) {
        if let Ok(c) = u8::try_from(value) {
            print!("{}", c as char);
        }
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let input = if std::env::args().nth(1).as_deref() == Some("--interactive") {
        VecDeque::new()
    }
    else {
        read_to_string("commands")?
            .lines()
            .rev()
            .flat_map(|line| format!("{line}\n").into_bytes())
            .map(Into::into)
            .collect()
    };
    let mut state = State { input };
    let mut computer = Computer::from_file("input", &mut state)?;
    computer.run();
    Ok(())
}
