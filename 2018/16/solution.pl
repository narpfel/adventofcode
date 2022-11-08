#!/usr/bin/env -S swipl -g main -t halt

:- use_module(library(dcg/basics)).
:- use_module(library(dcg/high_order)).

instruction([A, B, C, D]) -->
    integer(A), " ",
    integer(B), " ",
    integer(C), " ",
    integer(D), blanks.

example(example(Before, Instr, After)) -->
    "Before: [", sequence(integer, ", ", Before), "]", eol,
    instruction(Instr),
    "After:  [", sequence(integer, ", ", After), "]", blanks.

input(Examples, Instrs) -->
    sequence(example, Examples),
    sequence(instruction, Instrs).

execute(addr, Lhs, Rhs, Output, Before, After) :-
    nth0(Lhs, Before, LhsValue),
    nth0(Rhs, Before, RhsValue),
    Result is LhsValue + RhsValue,
    set_reg(Output, Result, Before, After).
execute(addi, Lhs, Rhs, Output, Before, After) :-
    nth0(Lhs, Before, LhsValue),
    Result is LhsValue + Rhs,
    set_reg(Output, Result, Before, After).
execute(mulr, Lhs, Rhs, Output, Before, After) :-
    nth0(Lhs, Before, LhsValue),
    nth0(Rhs, Before, RhsValue),
    Result is LhsValue * RhsValue,
    set_reg(Output, Result, Before, After).
execute(muli, Lhs, Rhs, Output, Before, After) :-
    nth0(Lhs, Before, LhsValue),
    Result is LhsValue * Rhs,
    set_reg(Output, Result, Before, After).
execute(banr, Lhs, Rhs, Output, Before, After) :-
    nth0(Lhs, Before, LhsValue),
    nth0(Rhs, Before, RhsValue),
    Result is LhsValue /\ RhsValue,
    set_reg(Output, Result, Before, After).
execute(bani, Lhs, Rhs, Output, Before, After) :-
    nth0(Lhs, Before, LhsValue),
    Result is LhsValue /\ Rhs,
    set_reg(Output, Result, Before, After).
execute(borr, Lhs, Rhs, Output, Before, After) :-
    nth0(Lhs, Before, LhsValue),
    nth0(Rhs, Before, RhsValue),
    Result is LhsValue \/ RhsValue,
    set_reg(Output, Result, Before, After).
execute(bori, Lhs, Rhs, Output, Before, After) :-
    nth0(Lhs, Before, LhsValue),
    Result is LhsValue \/ Rhs,
    set_reg(Output, Result, Before, After).
execute(setr, Lhs, _Rhs, Output, Before, After) :-
    nth0(Lhs, Before, LhsValue),
    set_reg(Output, LhsValue, Before, After).
execute(seti, Lhs, _Rhs, Output, Before, After) :-
    set_reg(Output, Lhs, Before, After).
execute(gtir, Lhs, Rhs, Output, Before, After) :-
    nth0(Rhs, Before, RhsValue),
    greater(Lhs, RhsValue, Result),
    set_reg(Output, Result, Before, After).
execute(gtri, Lhs, Rhs, Output, Before, After) :-
    nth0(Lhs, Before, LhsValue),
    greater(LhsValue, Rhs, Result),
    set_reg(Output, Result, Before, After).
execute(gtrr, Lhs, Rhs, Output, Before, After) :-
    nth0(Lhs, Before, LhsValue),
    nth0(Rhs, Before, RhsValue),
    greater(LhsValue, RhsValue, Result),
    set_reg(Output, Result, Before, After).
execute(eqir, Lhs, Rhs, Output, Before, After) :-
    nth0(Rhs, Before, RhsValue),
    equals(Lhs, RhsValue, Result),
    set_reg(Output, Result, Before, After).
execute(eqri, Lhs, Rhs, Output, Before, After) :-
    nth0(Lhs, Before, LhsValue),
    equals(LhsValue, Rhs, Result),
    set_reg(Output, Result, Before, After).
execute(eqrr, Lhs, Rhs, Output, Before, After) :-
    nth0(Lhs, Before, LhsValue),
    nth0(Rhs, Before, RhsValue),
    equals(LhsValue, RhsValue, Result),
    set_reg(Output, Result, Before, After).

set_reg(0, Val, [_, X, Y, Z], [Val, X, Y, Z]) :- !.
set_reg(1, Val, [W, _, Y, Z], [W, Val, Y, Z]) :- !.
set_reg(2, Val, [W, X, _, Z], [W, X, Val, Z]) :- !.
set_reg(3, Val, [W, X, Y, _], [W, X, Y, Val]) :- !.

greater(X, Y, 1) :- X > Y, !.
greater(_, _, 0).

equals(X, X, 1) :-  !.
equals(_, _, 0).

part1(Examples, Solution) :-
    include(
        [example(Before, [_, B, C, D], After)] >> (
            findall(Opcode, execute(Opcode, B, C, D, Before, After), Opcodes),
            length(Opcodes, N),
            N >= 3
        ),
        Examples,
        MatchesThreeOrMoreOpcodes
    ),
    length(MatchesThreeOrMoreOpcodes, Solution).

execute_with_mapping(OpcodeMapping, example(Before, Instr, After)) :-
    execute_with_mapping(OpcodeMapping, Instr, Before, After).
execute_with_mapping(OpcodeMapping, [A, B, C, D], Before, After) :-
    member(Opcode-A, OpcodeMapping),
    execute(Opcode, B, C, D, Before, After).

part2(Examples, Instrs, Solution) :-
    Opcodes = [
        addr-_,
        addi-_,
        mulr-_,
        muli-_,
        banr-_,
        bani-_,
        borr-_,
        bori-_,
        setr-_,
        seti-_,
        gtir-_,
        gtri-_,
        gtrr-_,
        eqir-_,
        eqri-_,
        eqrr-_
    ],
    maplist(execute_with_mapping(Opcodes), Examples),
    foldl(execute_with_mapping(Opcodes), Instrs, [0, 0, 0, 0], Registers),
    nth0(0, Registers, Solution).

main :-
    phrase_from_file(input(Examples, Instrs), input),
    part1(Examples, Part1),
    write(Part1), nl,
    part2(Examples, Instrs, Part2),
    write(Part2), nl.
