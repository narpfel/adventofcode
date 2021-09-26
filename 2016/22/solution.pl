#!/usr/bin/env -S swipl -g main -t halt

:- use_module(library(dcg/basics)).

parse_node(node(X, Y, Size, Used, Avail)) -->
    "/dev/grid/node-x", integer(X), "-y", integer(Y),
    blanks, integer(Size), "T", blanks,
    integer(Used), "T", blanks, integer(Avail), "T", blanks,
    integer(_), "%".

read_input(Filename, Nodes) :-
    open(Filename, read, Input),
    read_string(Input, "", "\n", _, String),
    split_string(String, "\n", "", [_, _ | Lines]),
    maplist(
        [Line, Node] >> (
            string_codes(Line, Codes),
            phrase(parse_node(Node), Codes)
        ),
        Lines,
        Nodes
    ).

viable_pair(Nodes, Node, OtherNode) :-
    select(Node, Nodes, Rest),
    Node = node(_, _, _, Used, _),
    Used =\= 0,
    select(OtherNode, Rest, _),
    OtherNode = node(_, _, _, _, Avail),
    Avail >= Used.

viable_pairs(Nodes, ViablePairs) :-
    findall(Node-OtherNode, viable_pair(Nodes, Node, OtherNode), ViablePairs).

part1(Nodes, Solution) :-
    viable_pairs(Nodes, Pairs),
    length(Pairs, Solution).

field_string(Nodes, S) :-
    viable_pairs(Nodes, ViablePairs),
    pairs_keys_values(ViablePairs, Ks, Vs),
    append(Ks, Vs, WalkableNodes),
    size(Nodes, X, Y),
    length(Grid, X),
    maplist([Line] >> length(Line, Y), Grid),
    append(Grid, Nodes),
    maplist(line_string(X, WalkableNodes), Grid, LineStrings),
    atomics_to_string(LineStrings, "\n", S).

line_string(X, ViablePairs, Line, S) :-
    maplist(node_string(X, ViablePairs), Line, List),
    atomics_to_string(List, S).

node_string(_, _, node(0, 0, _, _, _), "O").
node_string(XSize, _, node(X, 0, _, _, _), "G") :- X is XSize - 1.
node_string(_, _, node(_, _, _, 0, _), "_").
node_string(_, WalkableNodes, Node, S) :- member(Node, WalkableNodes) -> S = "."; S = "#".

size(Nodes, XRes, YRes) :-
    findall(X-Y, member(node(X, Y, _, _, _), Nodes), XYs),
    pairs_keys_values(XYs, Xs, Ys),
    max_list(Xs, X), max_list(Ys, Y),
    XRes is X + 1,
    YRes is Y + 1.

main :-
    read_input(input, Nodes),
    part1(Nodes, Solution),
    write(Solution), nl,
    field_string(Nodes, S),
    open(grid, write, File),
    write(File, S), write(File, "\n"),
    close(File).
