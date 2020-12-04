#!/usr/bin/env -S swipl -g main -t halt

:- use_module(library(dcg/basics)).
:- use_module(library(dcg/high_order)).

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

year(Begin, End) --> integer(Year), { between(Begin, End, Year) }.

valid_height --> integer(Height), "cm", { between(150, 193, Height) }.
valid_height --> integer(Height), "in", { between(59, 76, Height) }.

hair_colour --> "#", sequence(xdigit, HexDigits), { length(HexDigits, 6) }.

field_valid(byr-Year) :- phrase(year(1920, 2002), Year).
field_valid(iyr-Year) :- phrase(year(2010, 2020), Year).
field_valid(eyr-Year) :- phrase(year(2020, 2030), Year).
field_valid(hgt-Height) :- phrase(valid_height, Height).
field_valid(hcl-Colour) :- phrase(hair_colour, Colour).
field_valid(ecl-ColourString) :-
    atom_string(Colour, ColourString),
    memberchk(Colour, [amb, blu, brn, gry, grn, hzl, oth]).
field_valid(pid-Id) :- phrase(sequence(digit, Digits), Id), length(Digits, 9).

valid_passport(IsFieldValid, Passport) :-
    required_fields(Required),
    forall(
        member(Field, Required),
        (
            memberchk(Field-Value, Passport),
            string_codes(Value, ValueChars),
            call(IsFieldValid, Field-ValueChars)
        )
    ).

solve(Passports, IsFieldValid, Solution) :-
    include(valid_passport(IsFieldValid), Passports, Valid),
    length(Valid, Solution).

main :-
    read_input(input, Passports),
    solve(Passports, [_] >> true, Part1),
    write(Part1), nl,
    solve(Passports, field_valid, Part2),
    write(Part2), nl.
