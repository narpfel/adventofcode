#!/usr/bin/env -S swipl -g main -t halt

:- table bridge/4.

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

bridge(Pieces, End, Length, Strength) :-
    (Piece = NextEnd-End; Piece = End-NextEnd),
    select(Piece, Pieces, Rest),
    bridge(Rest, NextEnd, L, S),
    Length is L + 2,
    Strength is S + 2 * End.

bridge(_, End, 1, End).

bridge(Pieces, Length-Strength) :-
    bridge(Pieces, 0, Length, Strength).

main :-
    read_input("input", Pieces),
    findall(Bridge, bridge(Pieces, Bridge), Bridges),
    pairs_values(Bridges, Strengths),
    max_list(Strengths, Part1),
    write(Part1), nl,
    max_member(_-Part2, Bridges),
    write(Part2), nl.
