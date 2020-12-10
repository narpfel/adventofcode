#!/usr/bin/env node

const { readFileSync } = require("fs");
const _ = require("lodash");

const readInput = filename => {
    const input = readFileSync(filename, "utf-8")
        .trim()
        .split("\n")
        .map(s => Number.parseInt(s))
        .sort((a, b) => a - b);
    input.unshift(0);
    input.push(_.max(input) + 3);
    return input;
};

const tribonacci = _.memoize(n => {
    if (n < 0) { return 0; }
    if (n == 0) { return 1; }
    if (n == 1) { return 1; }
    return tribonacci(n - 1) + tribonacci(n - 2) + tribonacci(n - 3);
});

const solvePart1 = input => {
    const differences = _.zipWith(input, _.tail(input), _.flip(_.subtract));
    const counts = _.countBy(differences);
    return counts[1] * counts[3];
};

const solvePart2 = input => {
    const differences = _.zipWith(input, _.tail(input), _.flip(_.subtract));

    const groups = [[differences[0]]];
    _.forEach(_.tail(differences), diff => {
        if (_.last(groups)[0] != diff) {
            groups.push([]);
        }
        _.last(groups).push(diff);
    });

    return _(groups)
        .filter(group => group[0] == 1)
        .map('length')
        .filter(l => l > 1)
        .map(tribonacci)
        .reduce(_.multiply, 1);
};

const main = () => {
    const input = readInput("input");
    console.log(solvePart1(input));
    console.log(solvePart2(input));
}

main();
