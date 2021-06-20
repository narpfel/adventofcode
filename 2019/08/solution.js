#!/usr/bin/env node

"use strict";

const { readFileSync } = require("fs");
const _ = require("lodash");

const WIDTH = 25;
const HEIGHT = 6;

const count = needle => haystack => {
    let count = 0;
    for (const value of haystack) {
        if (value == needle) {
            count++;
        }
    }
    return count;
};

const transpose = array => _.zip.apply(_, array);

const main = () => {
    const input = readFileSync("input", "utf-8").trim().split("").map(s => Number.parseInt(s));
    const layers = _.chunk(input, WIDTH * HEIGHT);
    const solutionLayer = _.minBy(layers, count(0));
    console.log("%d", count(1)(solutionLayer) * count(2)(solutionLayer));
    const image = _(transpose(layers))
        .chain()
        .map(layer => layer.find(n => n !== 2))
        .map(c => " #X"[c])
        .chunk(WIDTH)
        .map(a => a.join(""))
        .join("\n")
        .value();
    console.log(image);
};

main();
