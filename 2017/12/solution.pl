#!/usr/bin/env -S swipl -g main -t halt

:- set_prolog_flag(double_quotes, codes).

connection(N, Ms) -->
    numeric(N),
    " <-> ",
    numbers(Ms).

numbers([N | Ms]) -->
    numeric(N),
    ", ",
    numbers(Ms).
numbers([N]) --> numeric(N).

numeric(N) -->
    digit(D),
    digits(Ds),
    { number_codes(N, [D | Ds]) }.

digit(D) -->
    [D],
    { code_type(D, digit) }.

digits([D | Ds]) -->
    digit(D),
    digits(Ds).
digits([]) --> [].


add_pipes(N, [M | Ms]) :-
    assert(pipe(N, M)),
    add_pipes(N, Ms).
add_pipes(_, []).

parse_connection(S) :-
    string_codes(S, L),
    phrase(connection(N, Ms), L),
    add_pipes(N, Ms).

connected(X, Y) :- connected(X, Y, []).
connected(X, X, _).
connected(X, Y, Trace) :-
    pipe(X, Z),
    \+ memberchk(Z, Trace),
    connected(Z, Y, [Z | Trace]).

connection_count(Start, Count) :-
    unique_solutions(connected(Start), Connections),
    length(Connections, Count).

all_programs(Programs) :-
    unique_solutions(pipe(_), Programs).

unique_solutions(Predicate, UniqueSolutions) :-
    findall(X, call(Predicate, X), AllSolutions),
    sort(AllSolutions, UniqueSolutions).

is_in_any_group([], _) :- false.
is_in_any_group([Base | Groups], Program) :-
    connected(Program, Base);
    is_in_any_group(Groups, Program).

select_unique_groups(Groups, Program) :-
    is_in_any_group(Groups, Program).
select_unique_groups([Program | _], Program).

all_groups(Groups) :-
    all_programs(Programs),
    maplist(select_unique_groups(Groups), Programs).


main :-
    open('input', read, Input),
    read_string(Input, "", "\n", _, String),
    split_string(String, "\n", "", Lines),
    maplist(parse_connection, Lines),
    connection_count(0, Count),
    write(Count), nl,
    all_groups(Groups),
    length(Groups, GroupCount),
    write(GroupCount), nl.
