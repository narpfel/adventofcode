#!/usr/bin/env -S swipl -g main -t halt

:- use_module(library(dcg/basics)).

required_fields([byr, iyr, eyr, hgt, hcl, ecl, pid]).

fields([cid | Required]) :- required_fields(Required).

field(Key-Value) -->
    { fields(Fields), member(Key, Fields), atom_string(Key, KeyStr) },
    KeyStr, ":", nonblanks(ValueChars),
    { string_codes(Value, ValueChars) }.

parse_passport([Field]) -->
    field(Field),
    blanks_to_nl.
parse_passport([Field | Fields]) -->
    field(Field),
    (whites; blanks_to_nl),
    parse_passport(Fields).

parse_passports([]) --> eos.
parse_passports([Passport | Passports]) -->
    parse_passport(Passport),
    blanks_to_nl,
    parse_passports(Passports).

read_input(Filename, Passports) :-
    open(Filename, read, Input),
    read_string(Input, _, String),
    string_codes(String, Codes),
    phrase(parse_passports(Passports), Codes).

valid_passport(Passport) :-
    required_fields(Required),
    forall(member(Field, Required), memberchk(Field-_, Passport)).

part1(Passports, Solution) :-
    include(valid_passport, Passports, Valid),
    length(Valid, Solution).

main :-
    read_input(input, Passports),
    part1(Passports, Part1),
    write(Part1), nl.
