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

part1(Nodes, Solution) :-
    findall(Node-OtherNode, viable_pair(Nodes, Node, OtherNode), Pairs),
    length(Pairs, Solution).

main :-
    read_input(input, Nodes),
    part1(Nodes, Solution),
    write(Solution), nl.
