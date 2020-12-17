#!/usr/bin/env -S swipl -g main -t halt

:- use_module(library(dcg/basics)).
:- use_module(library(dcg/high_order)).

parse_field(Name-Ranges) -->
    string_without(":", NameCodes), { string_codes(Name, NameCodes) }, ": ",
    ranges(Ranges), blanks_to_nl.

range(between(Begin, End)) --> integer(Begin), "-", integer(End).

ranges(Ranges) --> sequence(range, " or ", Ranges).

parse_ticket(Numbers) --> sequence(integer, ",", Numbers), { Numbers \= [] }.

parse_tickets([]) --> blanks_to_nl.
parse_tickets([Ticket | Tickets]) --> parse_ticket(Ticket), blanks_to_nl, parse_tickets(Tickets).

parse_input(Fields, MyTicket, NearbyTickets) -->
    sequence(parse_field, Fields), blanks_to_nl,
    "your ticket:", blanks_to_nl,
    parse_ticket(MyTicket), blanks_to_nl, blanks_to_nl,
    "nearby tickets:", blanks_to_nl,
    parse_tickets(NearbyTickets).

read_input(Filename, Fields, MyTicket, NearbyTickets) :-
    open(Filename, read, Input),
    read_string(Input, _, String),
    string_codes(String, Codes),
    phrase(parse_input(Fields, MyTicket, NearbyTickets), Codes).

is_valid(Fields, Value) :-
    member(_-Ranges, Fields),
    member(Range, Ranges),
    call(Range, Value).

part1(Fields, NearbyTickets, Solution) :-
    maplist(exclude(is_valid(Fields)), NearbyTickets, InvalidValues),
    flatten(InvalidValues, Flat),
    sum_list(Flat, Solution).

all_fields_valid(Fields, Ticket) :-
    include(is_valid(Fields), Ticket, Ticket).

is_field_valid(_-Ranges, Value) :- member(Range, Ranges), call(Range, Value).

all_valid(_, []).
all_valid(Field, [Value | Values]) :- is_field_valid(Field, Value), all_valid(Field, Values).

find_order([], NearbyTickets, []) :- flatten(NearbyTickets, []).
find_order(Fields, NearbyTickets, [Field | OrderedFields]) :-
    maplist([[Head | Tail], Head, Tail] >> (true), NearbyTickets, Heads, Tails), !,
    select(Field, Fields, RestFields),
    all_valid(Field, Heads),
    find_order(RestFields, Tails, OrderedFields).

part2(Fields, MyTicket, NearbyTickets, Solution) :-
    include(all_fields_valid(Fields), NearbyTickets, ValidTickets),
    find_order(Fields, [MyTicket | ValidTickets], OrderedFields), !,
    maplist(
        [FieldName-_, Value, FieldName-Value] >> (true),
        OrderedFields,
        MyTicket,
        OrderedTicket
    ),
    string_codes("departure", Departure),
    include(
        [Name-_] >> (string_codes(Name, NameCodes), prefix(Departure, NameCodes)),
        OrderedTicket,
        DepartureInfo
    ),
    foldl([_-Value, OldAcc, Acc] >> (Acc is Value * OldAcc), DepartureInfo, 1, Solution).

main :-
    read_input(input, Fields, MyTicket, NearbyTickets),
    part1(Fields, NearbyTickets, Part1),
    write(Part1), nl,
    part2(Fields, MyTicket, NearbyTickets, Part2),
    write(Part2), nl.
