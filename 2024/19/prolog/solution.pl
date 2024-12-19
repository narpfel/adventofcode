#!/usr/bin/env -S swipl -g main -t halt

:- use_module(library(dcg/basics)).
:- use_module(library(dcg/high_order)).
:- use_module(library(pure_input)).

patterns(Patterns) --> sequence(string_without(",\n"), ", ", Patterns), eol.

towel(Towel) --> string_without("\n", Towel), eol.

towels([]) --> eos.
towels([Towel | Towels]) --> towel(Towel), towels(Towels).

input(Patterns, Towels) --> patterns(Patterns), eol, towels(Towels).

:- table count_possibilities/2.

count_possibilities([], 1).
count_possibilities(Towel, N) :-
    findall(K, (append(Pattern, Rest, Towel), pattern(Pattern), count_possibilities(Rest, K)), Ks),
    sum_list(Ks, N).

main :-
    phrase_from_file(input(Patterns, Towels), input),
    maplist([Pattern] >> assertz(pattern(Pattern)), Patterns),
    maplist(count_possibilities, Towels, Possibilities),
    include(\=(0), Possibilities, PossibleTowels),
    length(PossibleTowels, Part1),
    write(Part1), nl,
    sum_list(Possibilities, Part2),
    write(Part2), nl.
