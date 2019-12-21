use std::path::Path;
use std::fs::read_to_string;
use std::num::ParseIntError;
use std::convert::TryInto;
use std::sync::mpsc::Sender;

use failure::Fallible;
use num_traits::FromPrimitive;
use num_derive::FromPrimitive;

type Cell = i64;
type Memory = Vec<Cell>;

#[derive(Debug, Copy, Clone, FromPrimitive)]
enum Mode {
    Position = 0,
    Immediate = 1,
    Relative = 2,
}
use Mode::*;

#[derive(Debug, Copy, Clone, FromPrimitive)]
enum Opcode {
    Add = 1,
    Multiply = 2,
    ReadInput = 3,
    WriteOutput = 4,
    JumpIfTrue = 5,
    JumpIfFalse = 6,
    LessThan = 7,
    Equals = 8,
    AdjustRelativeBase = 9,
    Halt = 99,
}

pub fn read_puzzle_input(path: impl AsRef<Path>) -> Fallible<Memory> {
    Ok(parse(&read_to_string(path)?)?)
}

pub fn parse(s: &str) -> Result<Memory, ParseIntError> {
    s
        .trim()
        .split(',')
        .map(|number| number.parse().map_err(Into::into))
        .collect()
}

pub struct Computer<Inputs: Iterator<Item = Cell>> {
    pub memory: Memory,
    inputs: Inputs,
    pub outputs: Sender<Cell>,
    ip: usize,
    rb: Cell,
}

impl<Inputs: Iterator<Item = Cell>> Computer<Inputs> {
    pub fn from_str(
        s: &str,
        inputs: Inputs,
        outputs: Sender<Cell>
    ) -> Result<Computer<Inputs>, ParseIntError> {
        let memory = parse(s)?;
        Ok(Computer { memory, inputs, outputs, ip: 0, rb: 0, })
    }

    pub fn from_file(
        path: impl AsRef<Path>,
        inputs: Inputs,
        outputs: Sender<Cell>
    ) -> Fallible<Computer<Inputs>> {
        Ok(Computer::from_str(&read_to_string(path)?, inputs, outputs)?)
    }

    fn lookup(&mut self, address: usize) -> Option<&mut Cell> {
        if address >= self.memory.len() {
            self.memory.resize(address + 1, 0);
        }
        self.memory.get_mut(address)
    }

    fn read(&mut self, mode: Mode) -> Option<&mut Cell> {
        let cell = match mode {
            Position => (*self.lookup(self.ip)?).try_into().ok()?,
            Immediate => self.ip,
            Relative => (*self.lookup(self.ip)? + self.rb).try_into().ok()?,
        };
        self.ip += 1;
        self.lookup(cell)
    }

    fn write(&mut self, address: Cell, value: Cell, mode: Mode) -> Option<()> {
        let address = match mode {
            Position => address,
            Immediate => None?,
            Relative => address + self.rb,
        };
        self.lookup(address.try_into().ok()?).map(|cell| *cell = value)
    }

    pub fn run(&mut self) -> Option<()> {
        loop {
            let opcode = *self.read(Immediate)?;
            let command = opcode % 100;
            let mut modes = opcode / 100;

            macro_rules! operation {
                (2, store_result, $f:expr) => {{
                    let a = *self.read(next_mode(&mut modes)?)?;
                    let b = *self.read(next_mode(&mut modes)?)?;
                    let target_addr = *self.read(Immediate)?;
                    self.write(target_addr, $f(a, b), next_mode(&mut modes)?)?;
                }};
                (2, $f:expr) => {{
                    let a = *self.read(next_mode(&mut modes)?)?;
                    let b = *self.read(next_mode(&mut modes)?)?;
                    $f(a, b);
                }};
                (1, $f:expr) => {{
                    let a = *self.read(next_mode(&mut modes)?)?;
                    $f(a);
                }};
                (0, store_result, $f:expr) => {{
                    let target_addr = *self.read(Immediate)?;
                    self.write(target_addr, $f(), next_mode(&mut modes)?)?;
                }};
            }

            use Opcode::*;
            match Opcode::from_i64(command)? {
                Add => operation!(2, store_result, |a, b| a + b),
                Multiply => operation!(2, store_result, |a, b| a * b),
                ReadInput => {
                    let input = self.inputs.next()?;
                    operation!(0, store_result, || input);
                },
                WriteOutput => operation!(1, |output|
                    self.outputs.send(output).expect("Could not write value to output")
                ),
                JumpIfTrue => operation!(2, |condition, target| {
                    if condition != 0 {
                        self.ip = target as usize
                    }
                }),
                JumpIfFalse => operation!(2, |condition, target| {
                    if condition == 0 {
                        self.ip = target as usize
                    }
                }),
                LessThan => operation!(2, store_result, |lhs, rhs| (lhs < rhs) as Cell),
                Equals => operation!(2, store_result, |lhs, rhs| (lhs == rhs) as Cell),
                AdjustRelativeBase => operation!(1, |offset| self.rb += offset),
                Halt => return Some(()),
            }

        }
    }
}

fn next_mode(modes: &mut Cell) -> Option<Mode> {
    let mode = *modes % 10;
    *modes /= 10;
    Mode::from_i64(mode)
}
