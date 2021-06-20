#!/usr/bin/env node

"use strict";

const input = [16, 12, 1, 0, 15, 7, 11];

const solve = (starting_numbers, turn_count) => {
    const number_to_turn = new Array(turn_count);
    number_to_turn.fill(-1);
    for (const [i, n] of starting_numbers.entries()) {
        number_to_turn[n] = i;
    }
    let last_spoken = starting_numbers[starting_numbers.length - 1];
    for (let turn = starting_numbers.length; turn < turn_count; ++turn) {
        const last_spoken_on_turn = number_to_turn[last_spoken];
        number_to_turn[last_spoken] = turn - 1;
        if (last_spoken_on_turn < 0) {
            last_spoken = 0;
        }
        else {
            last_spoken = turn - last_spoken_on_turn - 1;
        }
    }
    return last_spoken;
};

const main = () => {
    console.log(solve(input, 2020));
    console.log(solve(input, 30_000_000));
};

main();
