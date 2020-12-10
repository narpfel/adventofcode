#!/usr/bin/env node

const { readFileSync } = require("fs");
const _ = require("lodash");

const solve = filename => {
    const input = readFileSync(filename, "utf-8")
        .trim()
        .split("\n")
        .map(s => Number.parseInt(s))
        .sort((a, b) => a - b);
    input.unshift(0);
    input.push(_.max(input) + 3);

    const differences = _.zipWith(input, _.tail(input), (a, b) => b - a);
    const counts = _.countBy(differences);
    return counts[1] * counts[3];
};

const main = () => {
    console.log(solve("input"));
}

main();
