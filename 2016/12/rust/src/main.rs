use std::error::Error;
use std::fs::read_to_string;

use cpu::Cpu;
use cpu::ImmOrReg;
use cpu::Instruction;
use cpu::Register;

fn solve(c: i64, program: &[Instruction]) -> i64 {
    let mut cpu = Cpu::new([0, 0, c, 0], program);
    cpu.run();
    cpu.get(ImmOrReg::Reg(Register::A))
}

fn main() -> Result<(), Box<dyn Error>> {
    let src = read_to_string("input")?;
    let (rest, program) = cpu::parse::program::<()>(&src)?;
    assert!(rest.is_empty());
    println!("{}", solve(0, &program));
    println!("{}", solve(1, &program));
    Ok(())
}
