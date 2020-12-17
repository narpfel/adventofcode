#!/usr/bin/env -S swipl -g main -t halt

:- use_module(library(dcg/basics)).
:- use_module(library(dcg/high_order)).

parse_field(Name-Ranges) -->
    string_without(":", NameCodes), { string_codes(Name, NameCodes) }, ": ",
    ranges(Ranges), blanks_to_nl.

range(Begin-End) --> integer(Begin), "-", integer(End).

ranges(Ranges) --> sequence(range, " or ", Ranges).

parse_ticket(Numbers) --> sequence(integer, ",", Numbers).

parse_input(Fields, MyTicket, NearbyTickets) -->
    sequence(parse_field, Fields), blanks_to_nl,
    "your ticket:", blanks_to_nl,
    parse_ticket(MyTicket), blanks_to_nl, blanks_to_nl,
    "nearby tickets:", blanks_to_nl,
    sequence(parse_ticket, "\n", NearbyTickets).

read_input(Filename, Fields, MyTicket, NearbyTickets) :-
    open(Filename, read, Input),
    read_string(Input, _, String),
    string_codes(String, Codes),
    phrase(parse_input(Fields, MyTicket, NearbyTickets), Codes).

is_valid(Fields, Value) :-
    member(_-Ranges, Fields),
    member(Lo-Hi, Ranges),
    between(Lo, Hi, Value).

solve(Fields, NearbyTickets, Solution) :-
    maplist(exclude(is_valid(Fields)), NearbyTickets, InvalidValues),
    flatten(InvalidValues, Flat),
    sum_list(Flat, Solution).

main :-
    read_input(input, Fields, _, NearbyTickets),
    solve(Fields, NearbyTickets, Solution),
    write(Solution), nl.
