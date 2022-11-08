#!/usr/bin/env -S swipl -g main -t halt

:- use_module(library(dcg/basics)).
:- use_module(library(dcg/high_order)).
:- use_module(library(clpfd)).

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
    Result #= LhsValue + RhsValue,
    set_reg(Output, Result, Before, After).
execute(addi, Lhs, Rhs, Output, Before, After) :-
    nth0(Lhs, Before, LhsValue),
    Result #= LhsValue + Rhs,
    set_reg(Output, Result, Before, After).
execute(mulr, Lhs, Rhs, Output, Before, After) :-
    nth0(Lhs, Before, LhsValue),
    nth0(Rhs, Before, RhsValue),
    Result #= LhsValue * RhsValue,
    set_reg(Output, Result, Before, After).
execute(muli, Lhs, Rhs, Output, Before, After) :-
    nth0(Lhs, Before, LhsValue),
    Result #= LhsValue * Rhs,
    set_reg(Output, Result, Before, After).
execute(banr, Lhs, Rhs, Output, Before, After) :-
    nth0(Lhs, Before, LhsValue),
    nth0(Rhs, Before, RhsValue),
    Result #= LhsValue /\ RhsValue,
    set_reg(Output, Result, Before, After).
execute(bani, Lhs, Rhs, Output, Before, After) :-
    nth0(Lhs, Before, LhsValue),
    Result #= LhsValue /\ Rhs,
    set_reg(Output, Result, Before, After).
execute(borr, Lhs, Rhs, Output, Before, After) :-
    nth0(Lhs, Before, LhsValue),
    nth0(Rhs, Before, RhsValue),
    Result #= LhsValue \/ RhsValue,
    set_reg(Output, Result, Before, After).
execute(bori, Lhs, Rhs, Output, Before, After) :-
    nth0(Lhs, Before, LhsValue),
    Result #= LhsValue \/ Rhs,
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

greater(X, Y, 1) :- X #> Y, !.
greater(_, _, 0).

equals(X, Y, 1) :- X #= Y, !.
equals(_, _, 0).

part1(Examples, Solution) :-
    include(
        [example(Before, [_, B, C, D], After)] >> (
            findall(Opcode, execute(Opcode, B, C, D, Before, After), Opcodes),
            length(Opcodes, N),
            N #>= 3
        ),
        Examples,
        MatchesThreeOrMoreOpcodes
    ),
    length(MatchesThreeOrMoreOpcodes, Solution).

main :-
    phrase_from_file(input(Examples, _Instrs), input),
    part1(Examples, Part1),
    write(Part1), nl.
