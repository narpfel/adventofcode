#!/usr/bin/env -S swipl -g main -t halt

:- use_module(library(dcg/basics)).
:- use_module(library(pure_input)).

one_to_three_digit_integer(Int) --> integer(Int), { 0 =< Int, Int < 1000 }.

mul(Product) -->
    "mul(", one_to_three_digit_integer(Lhs), ",", one_to_three_digit_integer(Rhs), ")",
    { Product is Lhs * Rhs }.

conditional_mul(Value) --> mul(Value).
conditional_mul(0) --> "don't()", string(_), "do()".

multiplications(Mul, Result) -->
    string(_), call(Mul, Product), multiplications(Mul, Rest),
    { Result is Rest + Product }.
multiplications(_, 0) --> string(_), eos.

main :-
    phrase_from_file(multiplications(mul, Part1), input),
    write(Part1), nl,
    phrase_from_file(multiplications(conditional_mul, Part2), input),
    write(Part2), nl.
