#!/usr/bin/env -S swipl -g main -t halt

:- use_module(library(clpfd)).
:- use_module(library(dcg/basics)).
:- use_module(library(pure_input)).

machine(machine(Ax, Ay, Bx, By, Px, Py)) -->
    "Button A: X+", integer(Ax), ", Y+", integer(Ay), eol,
    "Button B: X+", integer(Bx), ", Y+", integer(By), eol,
    "Prize: X=", integer(Px), ", Y=", integer(Py), eol.

machines([Machine | Machines]) --> machine(Machine), blanks, machines(Machines).
machines([]) --> [].

cost(Offset, machine(Ax, Ay, Bx, By, Px, Py), Cost) :-
    [N, M] ins 0..sup,
    N * Ax + M * Bx #= Offset + Px,
    N * Ay + M * By #= Offset + Py,
    Cost #= 3 * N + M,
    labeling([min(Cost)], [Cost]).
cost(_, _, 0).

solve(Offset, Machines, Cost) :-
    maplist(cost(Offset), Machines, Costs),
    sum_list(Costs, Cost).

main :-
    phrase_from_file(machines(Machines), input),
    solve(0, Machines, Part1),
    write(Part1), nl,
    solve(10000000000000, Machines, Part2),
    write(Part2), nl.
