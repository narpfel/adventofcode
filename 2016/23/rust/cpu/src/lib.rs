#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Register {
    A,
    B,
    C,
    D,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ImmOrReg {
    Imm(i64),
    Reg(Register),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Instruction {
    Cpy(ImmOrReg, ImmOrReg),
    Inc(ImmOrReg),
    Dec(ImmOrReg),
    Jnz(ImmOrReg, ImmOrReg),
    Tgl(ImmOrReg),
    Add(Register, Register),
    Mul {
        target: Register,
        unchanged_factor: Register,
        mutated_factor: Register,
        scratch: Register,
    },
    Nop,
}

#[derive(Debug)]
pub struct Cpu {
    pc: i64,
    registers: [i64; 4],
    rom: Vec<Instruction>,
    original_rom: Vec<Instruction>,
    optimised: bool,
    can_optimise: bool,
    poisoned: Vec<bool>,
}

pub mod parse {
    use nom::branch::alt;
    use nom::bytes::complete::tag;
    use nom::character::complete::newline;
    use nom::character::complete::space1;
    use nom::combinator::map;
    use nom::combinator::value;
    use nom::error::ParseError;
    use nom::multi::many1;
    use nom::sequence::preceded;
    use nom::sequence::terminated;
    use nom::sequence::tuple;
    use nom::IResult;

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

    pub fn program<'a, E: ParseError<&'a str>>(
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
            Instruction::Add(_, _) => unreachable!(),
            Instruction::Mul { .. } => unreachable!(),
            Instruction::Nop => unreachable!(),
        }
    }
}

impl Cpu {
    pub fn new(registers: [i64; 4], original_rom: &[Instruction]) -> Self {
        let (optimised, poisoned, rom) = optimise(original_rom);
        Cpu {
            pc: 0,
            registers,
            rom,
            original_rom: original_rom.to_owned(),
            optimised,
            can_optimise: optimised,
            poisoned,
        }
    }

    pub fn get(&self, imm_or_reg: ImmOrReg) -> i64 {
        match imm_or_reg {
            ImmOrReg::Imm(imm) => imm,
            ImmOrReg::Reg(reg) => self.registers[reg as usize],
        }
    }

    fn get_mut(&mut self, reg: Register) -> &mut i64 {
        &mut self.registers[reg as usize]
    }

    pub fn run(&mut self) {
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
                    self.deoptimise_if_poisoned(self.pc);
                    if self.can_optimise && !self.optimised {
                        (self.optimised, self.poisoned, self.rom) = optimise(&self.original_rom);
                        self.can_optimise = self.optimised;
                    }
                },
            Instruction::Tgl(src) => {
                if let Some(instr) = usize::try_from(self.pc + self.get(src))
                    .ok()
                    .and_then(|idx| {
                        self.deoptimise_if_poisoned(idx);
                        self.rom.get_mut(idx)
                    })
                {
                    *instr = instr.toggle();
                    self.can_optimise = true;
                }
            }
            Instruction::Add(dst, src) => {
                *self.get_mut(dst) += self.get(ImmOrReg::Reg(src));
                *self.get_mut(src) = 0;
            }
            Instruction::Mul {
                target,
                unchanged_factor,
                mutated_factor,
                scratch,
            } => {
                *self.get_mut(target) =
                    *self.get_mut(unchanged_factor) * *self.get_mut(mutated_factor);
                *self.get_mut(scratch) = 0;
                *self.get_mut(mutated_factor) = 0;
            }
            _ => (),
        }
    }

    fn deoptimise_if_poisoned<T>(&mut self, idx: T)
    where
        usize: TryFrom<T>,
    {
        if let Some(true) = usize::try_from(idx)
            .ok()
            .and_then(|idx| self.poisoned.get(idx))
        {
            self.rom.clone_from(&self.original_rom);
            self.poisoned.iter_mut().for_each(|x| *x = false);
            self.optimised = false;
        }
    }
}

fn optimise(original_program: &[Instruction]) -> (bool, Vec<bool>, Vec<Instruction>) {
    use ImmOrReg::*;
    use Instruction::*;

    let mut program = original_program.to_vec();

    for i in 0..program.len() - 2 {
        match program[i..=i + 2] {
            [Inc(Reg(dst)), Dec(Reg(src)), Jnz(Reg(c), Imm(-2))]
            | [Dec(Reg(src)), Inc(Reg(dst)), Jnz(Reg(c), Imm(-2))]
                if src == c =>
            {
                program[i] = Add(dst, src);
                program[i + 1] = Nop;
                program[i + 2] = Nop;
            }
            _ => {}
        }
    }

    for i in 0..program.len() - 5 {
        match program[i..=i + 5] {
            [Cpy(Reg(unchanged_factor), Reg(scratch)), Add(target, also_scratch), Nop, Nop, Dec(Reg(mutated_factor)), Jnz(Reg(also_mutated_factor), Imm(-5))]
                if scratch == also_scratch && mutated_factor == also_mutated_factor =>
            {
                program[i] = Mul {
                    target,
                    unchanged_factor,
                    mutated_factor,
                    scratch,
                };
                program[i + 1] = Nop;
                program[i + 2] = Nop;
                program[i + 3] = Nop;
                program[i + 4] = Nop;
            }
            _ => {}
        }
    }

    let poisoned: Vec<_> = program
        .iter()
        .zip(original_program)
        .map(|(a, b)| a != b)
        .collect();
    (poisoned.iter().any(|&p| p), poisoned, program)
}
