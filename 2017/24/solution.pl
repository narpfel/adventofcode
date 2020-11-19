#!/usr/bin/env -S swipl -g main -t halt

read_input(Filename, Pieces) :-
    open(Filename, read, Input),
    read_string(Input, "", "\n", _, String),
    split_string(String, "\n", "", Lines),
    maplist(
        [Line, A-B] >> (
            split_string(Line, "/", "", NumberStrings),
            maplist(atom_number, NumberStrings, [A, B])
        ),
        Lines,
        Pieces
    ).

bridge(Pieces, End, Ports, Result) :-
    (Piece = NextEnd-End; Piece = End-NextEnd),
    select(Piece, Pieces, Rest),
    bridge(Rest, NextEnd, [End, End | Ports], Result).

bridge(_, End, Ports, [End | Ports]).

bridge(Pieces, Strength) :-
    bridge(Pieces, 0, [], Ports),
    sum_list(Ports, Strength).

main :-
    read_input("input", Pieces),
    findall(Strength, bridge(Pieces, Strength), Strengths),
    max_list(Strengths, Solution),
    write(Solution), nl.
