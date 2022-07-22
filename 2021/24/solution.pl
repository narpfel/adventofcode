#!/usr/bin/env -S swipl -g main -t halt

:- use_module(library(clpfd)).
:- use_module(library(dcg/basics)).

instruction(inp(Reg, Val)) --> "inp ", register(Reg), { Val in 1..9 }.
instruction(add(Dest, Src)) --> "add ", register(Dest), blanks, source_operand(Src).
instruction(mul(Dest, Src)) --> "mul ", register(Dest), blanks, source_operand(Src).
instruction(div(Dest, Src)) --> "div ", register(Dest), blanks, source_operand(Src).
instruction(mod(Dest, Src)) --> "mod ", register(Dest), blanks, source_operand(Src).
instruction(eql(Dest, Src)) --> "eql ", register(Dest), blanks, source_operand(Src).

instructions([Instr | Instrs]) --> instruction(Instr), blanks, instructions(Instrs).
instructions([]) --> [].

source_operand(Int) --> integer(Int), !.
source_operand(Reg) --> register(Reg).

register(reg(Reg)) --> nonblanks(Codes), { atom_codes(Reg, Codes) }.

evaluate(Regs, [inp(Reg, Val) | Instrs], ResultRegs, [Val | Vars]) :-
    set_reg(Reg, Val, Regs, NewRegs),
    evaluate(NewRegs, Instrs, ResultRegs, Vars).
evaluate(Regs, [add(Dest, Src) | Instrs], ResultRegs, Vars) :-
    read_operand(Dest, Regs, DestVal),
    read_operand(Src, Regs, SrcVal),
    NewVal #= DestVal + SrcVal,
    set_reg(Dest, NewVal, Regs, NewRegs),
    evaluate(NewRegs, Instrs, ResultRegs, Vars).
evaluate(Regs, [mul(Dest, Src) | Instrs], ResultRegs, Vars) :-
    read_operand(Dest, Regs, DestVal),
    read_operand(Src, Regs, SrcVal),
    NewVal #= DestVal * SrcVal,
    set_reg(Dest, NewVal, Regs, NewRegs),
    evaluate(NewRegs, Instrs, ResultRegs, Vars).
evaluate(Regs, [div(Dest, Src) | Instrs], ResultRegs, Vars) :-
    read_operand(Dest, Regs, DestVal),
    read_operand(Src, Regs, SrcVal),
    SrcVal #\= 0,
    NewVal #= DestVal // SrcVal,
    set_reg(Dest, NewVal, Regs, NewRegs),
    evaluate(NewRegs, Instrs, ResultRegs, Vars).
evaluate(Regs, [mod(Dest, Src) | Instrs], ResultRegs, Vars) :-
    read_operand(Dest, Regs, DestVal),
    read_operand(Src, Regs, SrcVal),
    DestVal #>= 0,
    SrcVal #> 0,
    NewVal #= DestVal rem SrcVal,
    set_reg(Dest, NewVal, Regs, NewRegs),
    evaluate(NewRegs, Instrs, ResultRegs, Vars).
evaluate(Regs, [eql(Dest, Src) | Instrs], ResultRegs, Vars) :-
    read_operand(Dest, Regs, DestVal),
    read_operand(Src, Regs, SrcVal),
    equals(DestVal, SrcVal, NewVal),
    set_reg(Dest, NewVal, Regs, NewRegs),
    evaluate(NewRegs, Instrs, ResultRegs, Vars).
evaluate(Regs, [], Regs, []).

equals(A, B, 1) :- A #= B, !.
equals(_, _, 0).

read_operand(reg(w), [W, _, _, _], W) :- !.
read_operand(reg(x), [_, X, _, _], X) :- !.
read_operand(reg(y), [_, _, Y, _], Y) :- !.
read_operand(reg(z), [_, _, _, Z], Z) :- !.
read_operand(Immediate, _, Immediate).

set_reg(reg(w), Val, [_, X, Y, Z], [Val, X, Y, Z]) :- !.
set_reg(reg(x), Val, [W, _, Y, Z], [W, Val, Y, Z]) :- !.
set_reg(reg(y), Val, [W, X, _, Z], [W, X, Val, Z]) :- !.
set_reg(reg(z), Val, [W, X, Y, _], [W, X, Y, Val]) :- !.
set_reg(Reg, _, _, _) :- throw(invalid_reg(Reg)).

reverse_digits_int([A], A).
reverse_digits_int([A | Rest], Result) :-
    reverse_digits_int(Rest, B),
    Result #= A + 10 * B.

solve(Predicate, Solution) :-
    phrase_from_file(instructions(Instructions), "input"),
    evaluate([0, 0, 0, 0], Instructions, [_, _, _, Z], Digits),
    Z #= 0,
    labeling([Predicate], Digits),
    reverse(ReverseDigits, Digits),
    reverse_digits_int(ReverseDigits, Solution).

main :-
    solve(down, Part1),
    write(Part1), nl,
    solve(up, Part2),
    write(Part2), nl.
