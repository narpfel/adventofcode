#!/usr/bin/env -S ruby --enable=jit

MODULUS = 2147483647

def lehmer_rng m, a, x
  (a * x) % m
end

def part1 a, b
  result = 0

  40_000_000.times do
    a = lehmer_rng MODULUS, 16807, a
    b = lehmer_rng MODULUS, 48271, b
    result += if (a & 0xffff) == (b & 0xffff) then 1 else 0 end
  end

  result
end

def part2 a, b
  result = 0

  5_000_000.times do
    loop do
      a = lehmer_rng MODULUS, 16807, a
      break if (a % 4) == 0
    end
    loop do
      b = lehmer_rng MODULUS, 48271, b
      break if (b % 8) == 0
    end
    result += if (a & 0xffff) == (b & 0xffff) then 1 else 0 end
  end

  result
end

def main()
  puts part1 116, 299
  puts part2 116, 299
end

main if __FILE__ == $0
