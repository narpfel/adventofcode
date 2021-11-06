use std::{
    error::Error,
    fs::read_to_string,
};

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Register {
    A,
    B,
    C,
    D,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum ImmOrReg {
    Imm(i64),
    Reg(Register),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Instruction {
    Cpy(ImmOrReg, ImmOrReg),
    Inc(ImmOrReg),
    Dec(ImmOrReg),
    Jnz(ImmOrReg, ImmOrReg),
    Tgl(ImmOrReg),
}

#[derive(Debug)]
struct Cpu {
    pc: i64,
    registers: [i64; 4],
    rom: Vec<Instruction>,
}

mod parse {
    use nom::{
        branch::alt,
        bytes::complete::tag,
        character::complete::{
            newline,
            space1,
        },
        combinator::{
            map,
            value,
        },
        error::ParseError,
        multi::many1,
        sequence::{
            preceded,
            terminated,
            tuple,
        },
        IResult,
    };

    use super::*;

    fn register<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Register, E> {
        alt((
            value(Register::A, tag("a")),
            value(Register::B, tag("b")),
            value(Register::C, tag("c")),
            value(Register::D, tag("d")),
        ))(input)
    }

    fn immediate_or_register<'a, E: ParseError<&'a str>>(
        input: &'a str,
    ) -> IResult<&'a str, ImmOrReg, E> {
        alt((
            map(nom::character::complete::i64, ImmOrReg::Imm),
            map(register, ImmOrReg::Reg),
        ))(input)
    }

    fn instruction<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Instruction, E> {
        let mnemonic = |name| preceded(preceded(tag(name), space1), immediate_or_register);
        let mnemonic2 = |name| tuple((mnemonic(name), preceded(space1, immediate_or_register)));

        alt((
            map(mnemonic2("cpy"), |(a, b)| Instruction::Cpy(a, b)),
            map(mnemonic("inc"), Instruction::Inc),
            map(mnemonic("dec"), Instruction::Dec),
            map(mnemonic2("jnz"), |(a, b)| Instruction::Jnz(a, b)),
            map(mnemonic("tgl"), Instruction::Tgl),
        ))(input)
    }

    pub(super) fn program<'a, E: ParseError<&'a str>>(
        input: &'a str,
    ) -> IResult<&'a str, Vec<Instruction>, E> {
        many1(terminated(instruction, newline))(input)
    }
}

impl Instruction {
    fn toggle(self) -> Instruction {
        match self {
            Instruction::Cpy(a, b) => Instruction::Jnz(a, b),
            Instruction::Inc(a) => Instruction::Dec(a),
            Instruction::Dec(a) => Instruction::Inc(a),
            Instruction::Jnz(a, b) => Instruction::Cpy(a, b),
            Instruction::Tgl(a) => Instruction::Inc(a),
        }
    }
}

impl Cpu {
    fn get(&self, imm_or_reg: ImmOrReg) -> i64 {
        match imm_or_reg {
            ImmOrReg::Imm(imm) => imm,
            ImmOrReg::Reg(reg) => self.registers[reg as usize],
        }
    }

    fn get_mut(&mut self, reg: Register) -> &mut i64 {
        &mut self.registers[reg as usize]
    }

    fn run(&mut self) {
        while let Some(&instruction) = usize::try_from(self.pc)
            .ok()
            .and_then(|pc| self.rom.get(pc))
        {
            self.execute(instruction);
            self.pc += 1;
        }
    }

    fn execute(&mut self, instruction: Instruction) {
        match instruction {
            Instruction::Cpy(src, ImmOrReg::Reg(dst)) => *self.get_mut(dst) = self.get(src),
            Instruction::Inc(ImmOrReg::Reg(reg)) => *self.get_mut(reg) += 1,
            Instruction::Dec(ImmOrReg::Reg(reg)) => *self.get_mut(reg) -= 1,
            Instruction::Jnz(src, offset) =>
                if self.get(src) != 0 {
                    self.pc += self.get(offset) - 1;
                },
            Instruction::Tgl(src) =>
                if let Some(instr) = usize::try_from(self.pc + self.get(src))
                    .ok()
                    .and_then(|idx| self.rom.get_mut(idx))
                {
                    *instr = instr.toggle();
                },
            _ => (),
        }
    }
}

fn solve(a: i64, program: &[Instruction]) -> i64 {
    let mut cpu = Cpu {
        pc: 0,
        registers: [a, 0, 0, 0],
        rom: program.to_owned(),
    };
    cpu.run();
    cpu.get(ImmOrReg::Reg(Register::A))
}

fn main() -> Result<(), Box<dyn Error>> {
    let src = read_to_string("input")?;
    let (rest, program) = parse::program::<()>(&src)?;
    assert!(rest.is_empty());
    println!("{}", solve(7, &program));
    println!("{}", solve(12, &program));
    Ok(())
}
