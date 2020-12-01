#!/usr/bin/env -S swipl -g main -t halt

read_input(Filename, Expenses) :-
    open(Filename, read, Input),
    read_string(Input, "", "\n", _, String),
    split_string(String, "\n", "", Lines),
    maplist([Line, Expense] >> (number_string(Expense, Line)), Lines, Expenses).

part1(Expenses, Solution) :-
    select(A, Expenses, Rest),
    select(B, Rest, _),
    2020 is A + B,
    Solution is A * B.

part2(Expenses, Solution) :-
    select(A, Expenses, Rest),
    select(B, Rest, Rest2),
    select(C, Rest2, _),
    2020 is A + B + C,
    Solution is A * B * C.

main :-
    read_input(input, Expenses),
    part1(Expenses, Part1),
    write(Part1), nl,
    part2(Expenses, Part2),
    write(Part2), nl.
