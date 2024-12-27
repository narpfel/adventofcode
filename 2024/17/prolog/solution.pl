#!/usr/bin/env -S swipl -g main -t halt

:- use_module(library(clpfd)).
:- use_module(library(dcg/basics)).
:- use_module(library(dcg/high_order)).
:- use_module(library(pure_input)).

input([A, B, C], Program) -->
    "Register A: ", integer(A), eol,
    "Register B: ", integer(B), eol,
    "Register C: ", integer(C), eol,
    eol,
    "Program: ", sequence(number, ",", Program), eol.

combo(_, 0, 0).
combo(_, 1, 1).
combo(_, 2, 2).
combo(_, 3, 3).
combo([A, _, _], 4, A).
combo([_, B, _], 5, B).
combo([_, _, C], 6, C).

divide(Operand, [Numerator, B, C], Result) :-
    combo([Numerator, B, C], Operand, Denominator),
    Result #= Numerator >> Denominator.

run(0, Operand, Pc, Pc + 2, [A, B, C], [NewA, B, C], []) :-
    divide(Operand, [A, B, C], NewA).
run(1, Operand, Pc, Pc + 2, [A, B, C], [A, NewB, C], []) :-
    NewB #= B xor Operand.
run(2, Operand, Pc, Pc + 2, [A, B, C], [A, NewB, C], []) :-
    combo([A, B, C], Operand, ComboOp),
    NewB #= ComboOp /\ 0b111.
run(3, Operand, _, Operand, [A, B, C], [A, B, C], []) :-
    A #\= 0.
run(3, _, Pc, Pc + 2, [A, B, C], [A, B, C], []) :-
    A #= 0.
run(4, _, Pc, Pc + 2, [A, B, C], [A, NewB, C], []) :-
    NewB #= B xor C.
run(5, Operand, Pc, Pc + 2, [A, B, C], [A, B, C], [Output]) :-
    combo([A, B, C], Operand, ComboOp),
    Output #= ComboOp /\ 0b111.
run(6, Operand, Pc, Pc + 2, [A, B, C], [A, NewB, C], []) :-
    divide(Operand, [A, B, C], NewB).
run(7, Operand, Pc, Pc + 2, [A, B, C], [A, B, NewC], []) :-
    divide(Operand, [A, B, C], NewC).

interpret(Program, Pc, Registers, NewOutputs, [A | As]) :-
    nth0(Pc, Program, Instr),
    OperandPc #= Pc + 1,
    nth0(OperandPc, Program, Operand),
    !,
    run(Instr, Operand, Pc, PcUpdate, Registers, NewRegisters, Output),
    [A | _] = NewRegisters,
    (Output = [Value] -> NewOutputs = [Value | Outputs]; NewOutputs = Outputs),
    NewPc #= PcUpdate,
    interpret(Program, NewPc, NewRegisters, Outputs, As).
interpret(_, _, _, [], []).

main :-
    phrase_from_file(input(Registers, Program), input),
    interpret(Program, 0, Registers, Output, _),
    atomic_list_concat(Output, ',', Part1),
    write(Part1), nl,
    interpret(Program, 0, [Part2, 0, 0], Program, As),
    reverse(As, ReverseAs),
    labeling([min(Part2)], ReverseAs),
    write(Part2), nl.
