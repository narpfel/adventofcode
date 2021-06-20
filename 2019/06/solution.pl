#!/usr/bin/env -S swipl -g main -t halt

orbit(Center, Orbiting) -->
    many(alnum, Center), ")", many(alnum, Orbiting).

many(_, []) --> [].
many(Type, [C | Cs]) -->
    [C], { code_type(C, Type) },
    many(Type, Cs).

parse_orbit(Orbit, String) :-
    string_codes(String, Codes),
    phrase(orbit(Center, Orbiting), Codes),
    string_codes(CenterStr, Center),
    string_codes(OrbitingStr, Orbiting),
    Orbit = directly_orbits(CenterStr, OrbitingStr).

orbits(X, Y) :-
    directly_orbits(X, Y);
    directly_orbits(X, Z), orbits(Z, Y).

bidirectional_orbit(X, Y) :-
    directly_orbits(X, Y);
    directly_orbits(Y, X).

read_input(FileName, Lines) :-
    open(FileName, read, Input),
    read_string(Input, "", "\n", _, String),
    split_string(String, "\n", "", Lines).

part1(Result) :-
    findall([X, Y], orbits(X, Y), AllOrbits),
    length(AllOrbits, Result).

part2(End, End, Trace, Result) :-
    directly_orbits(End, "SAN"),
    Trace = Result.

part2(Body, End, Trace, Result) :-
    bidirectional_orbit(Body, X),
    \+ memberchk(X, Trace),
    part2(X, End, [X | Trace], Result).

part2(Result) :-
    directly_orbits(Start, "YOU"),
    directly_orbits(End, "SAN"),
    findall(Path, part2(Start, End, [], Path), Paths),
    maplist(length, Paths, Lengths),
    min_list(Lengths, Result).


main :-
    read_input("input", Lines),
    maplist(parse_orbit, Orbits, Lines),
    maplist(assertz, Orbits),
    part1(Part1),
    write(Part1), nl,
    part2(Part2),
    write(Part2), nl.
