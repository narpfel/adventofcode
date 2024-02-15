#![feature(lint_reasons)]

use std::error::Error;
use std::fs::read_to_string;
use std::num::ParseIntError;
use std::path::Path;

pub type Cell = i64;
pub type Memory = Vec<Cell>;

#[derive(Debug, Copy, Clone)]
enum Mode {
    Position = 0,
    Immediate = 1,
    Relative = 2,
}
use Mode::*;

#[derive(Copy, Clone, Debug)]
pub struct InvalidMode(#[expect(dead_code)] Cell);

impl TryFrom<Cell> for Mode {
    type Error = InvalidMode;

    fn try_from(cell: Cell) -> Result<Self, InvalidMode> {
        let result = match cell {
            0 => Position,
            1 => Immediate,
            2 => Relative,
            _ => return Err(InvalidMode(cell)),
        };
        debug_assert_eq!(cell, result as Cell);
        Ok(result)
    }
}

#[derive(Debug, Copy, Clone)]
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

#[derive(Copy, Clone, Debug)]
pub struct InvalidOpcode(#[expect(dead_code)] Cell);

impl TryFrom<Cell> for Opcode {
    type Error = InvalidOpcode;

    fn try_from(cell: Cell) -> Result<Self, InvalidOpcode> {
        use Opcode::*;
        let result = match cell {
            1 => Add,
            2 => Multiply,
            3 => ReadInput,
            4 => WriteOutput,
            5 => JumpIfTrue,
            6 => JumpIfFalse,
            7 => LessThan,
            8 => Equals,
            9 => AdjustRelativeBase,
            99 => Halt,
            _ => return Err(InvalidOpcode(cell)),
        };
        debug_assert_eq!(cell, result as Cell);
        Ok(result)
    }
}

pub fn read_puzzle_input(path: impl AsRef<Path>) -> Result<Memory, Box<dyn Error>> {
    Ok(parse(&read_to_string(path)?)?)
}

pub fn parse(s: &str) -> Result<Memory, ParseIntError> {
    s.trim()
        .split(',')
        .map(|number| number.parse().map_err(Into::into))
        .collect()
}

pub struct Computer<'a, T: IO> {
    pub memory: Memory,
    io: &'a mut T,
    ip: usize,
    rb: Cell,
}

impl<'a, T: IO> Computer<'a, T> {
    pub fn new(memory: Memory, io: &'a mut T) -> Self {
        Self { memory, io, ip: 0, rb: 0 }
    }

    pub fn from_str(s: &str, io: &'a mut T) -> Result<Self, ParseIntError> {
        let memory = parse(s)?;
        Ok(Self::new(memory, io))
    }

    pub fn from_file(path: impl AsRef<Path>, io: &'a mut T) -> Result<Self, Box<dyn Error>> {
        Ok(Computer::from_str(&read_to_string(path)?, io)?)
    }

    fn lookup(&mut self, address: usize) -> Option<&mut Cell> {
        if address >= self.memory.len() {
            self.memory.resize(address + 1, 0);
        }
        self.memory.get_mut(address)
    }

    #[inline(always)]
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
        self.lookup(address.try_into().ok()?)
            .map(|cell| *cell = value)
    }

    pub fn step(&mut self) -> Option<bool> {
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
            (0, store_result, $value:expr) => {{
                let target_addr = *self.read(Immediate)?;
                self.write(target_addr, $value, next_mode(&mut modes)?)?;
            }};
        }

        use Opcode::*;
        match Opcode::try_from(command).ok()? {
            Add => operation!(2, store_result, |a, b| a + b),
            Multiply => operation!(2, store_result, |a, b| a * b),
            ReadInput => {
                let input = self.io.next_input()?;
                operation!(0, store_result, input);
            }
            WriteOutput => operation!(1, |output| self.io.output(output)),
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
            Halt => return Some(true),
        }
        Some(false)
    }

    pub fn run(&mut self) -> Option<()> {
        while !self.step()? {}
        Some(())
    }
}

fn next_mode(modes: &mut Cell) -> Option<Mode> {
    let mode = *modes % 10;
    *modes /= 10;
    Mode::try_from(mode).ok()
}

pub trait IO {
    fn next_input(&mut self) -> Option<Cell>;
    fn output(&mut self, value: Cell);
}
