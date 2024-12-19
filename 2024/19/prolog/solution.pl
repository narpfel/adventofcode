#!/usr/bin/env -S swipl -g main -t halt

:- use_module(library(dcg/basics)).
:- use_module(library(dcg/high_order)).
:- use_module(library(pure_input)).

patterns(Patterns) --> sequence(string_without(",\n"), ", ", Patterns), eol.

design(Design) --> string_without("\n", Design), eol.

designs([]) --> eos.
designs([Design | Designs]) --> design(Design), designs(Designs).

input(Patterns, Designs) --> patterns(Patterns), eol, designs(Designs).

:- table count_possibilities/2.

count_possibilities([], 1).
count_possibilities(Design, N) :-
    findall(K, (append(Pattern, Rest, Design), pattern(Pattern), count_possibilities(Rest, K)), Ks),
    sum_list(Ks, N).

main :-
    phrase_from_file(input(Patterns, Designs), input),
    maplist([Pattern] >> assertz(pattern(Pattern)), Patterns),
    maplist(count_possibilities, Designs, Possibilities),
    include(\=(0), Possibilities, PossibleDesigns),
    length(PossibleDesigns, Part1),
    write(Part1), nl,
    sum_list(Possibilities, Part2),
    write(Part2), nl.
