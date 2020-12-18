#!/usr/bin/env -S swipl -g main -t halt

:- use_module(library(dcg/basics)).
:- use_module(library(dcg/high_order)).
:- use_module(library(clpfd)).

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

valid_fields(_, [], []).
valid_fields(Fields, [Column | Tickets], [Valid | Rest]) :-
    include([Field] >> (all_valid(Field, Column)), Fields, ValidFields),
    pairs_keys(ValidFields, Valid),
    valid_fields(Fields, Tickets, Rest).

find_order(Fields, TicketsByColumn, OrderedFields) :-
    valid_fields(Fields, TicketsByColumn, ValidFields),
    foldl(
        [Batch, Acc, [Field | Acc]] >> (
            subtract(Batch, Acc, Options),
            member(Field, Options)
        ),
        ValidFields,
        [],
        ReverseOrderedFields
    ),
    reverse(ReverseOrderedFields, OrderedFields).

part2(Fields, MyTicket, NearbyTickets, Solution) :-
    include(all_fields_valid(Fields), NearbyTickets, ValidTickets),
    transpose([MyTicket | ValidTickets], TransposedTickets),
    find_order(Fields, TransposedTickets, OrderedFields), !,
    pairs_keys_values(TicketWithNames, OrderedFields, MyTicket),
    string_codes("departure", Departure),
    include(
        [Name-_] >> (string_codes(Name, NameCodes), prefix(Departure, NameCodes)),
        TicketWithNames,
        DepartureInfo
    ),
    foldl([_-Value, OldAcc, Acc] >> (Acc is Value * OldAcc), DepartureInfo, 1, Solution).

main :-
    read_input(input, Fields, MyTicket, NearbyTickets),
    part1(Fields, NearbyTickets, Part1),
    write(Part1), nl,
    part2(Fields, MyTicket, NearbyTickets, Part2),
    write(Part2), nl.
