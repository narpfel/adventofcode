#!/usr/bin/env node

const MODULUS = 2147483647;

const lehmer_rng = (m, a, x) => {
    return (a * x) % m;
};

const part1 = (a, b) => {
    let result = 0;
    for (let i = 0; i < 40_000_000; ++i) {
        a = lehmer_rng(MODULUS, 16807, a);
        b = lehmer_rng(MODULUS, 48271, b);
        result += (a & 0xffff) == (b & 0xffff);
    }
    return result;
};

const part2 = (a, b) => {
    let result = 0;
    for (let i = 0; i < 5_000_000; ++i) {
        // `while (true)` is disallowed by eslint. WAT‽
        for (;;) {
            a = lehmer_rng(MODULUS, 16807, a);
            if ((a % 4) == 0) {
                break;
            }
        }
        for (;;) {
            b = lehmer_rng(MODULUS, 48271, b);
            if ((b % 8) == 0) {
                break;
            }
        }
        result += (a & 0xffff) == (b & 0xffff);
    }
    return result;
};

const main = () => {
    console.log("%d", part1(116, 299));
    console.log("%d", part2(116, 299));
};

main();
