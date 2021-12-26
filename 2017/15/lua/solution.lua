#!/usr/bin/env luajit

MODULUS = 2147483647

function lehmer_rng(m, a, x)
    return (a * x) % m
end

function part1(a, b)
    local result = 0
    for _ = 1, 40000000 do
        a = lehmer_rng(MODULUS, 16807, a)
        b = lehmer_rng(MODULUS, 48271, b)
        result = result + (bit.band(a, 0xffff) == bit.band(b, 0xffff) and 1 or 0)
    end

    return result
end

function part2(a, b)
    local result = 0

    for i = 1, 5000000 do
        while true do
            a = lehmer_rng(MODULUS, 16807, a)
            if (a % 4) == 0 then
                break
            end
        end
        while true do
            b = lehmer_rng(MODULUS, 48271, b)
            if (b % 8) == 0 then
                break
            end
        end
        result = result + (bit.band(a, 0xffff) == bit.band(b, 0xffff) and 1 or 0)
    end

    return result
end

print(part1(116, 299))
print(part2(116, 299))
