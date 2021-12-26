#!/usr/bin/env ruby

INPUT = "16,12,1,0,15,7,11"

def parse_input starting_numbers
  starting_numbers.split(",").map &:to_i
end

def solve starting_numbers, turn_count
  number_to_turn = [-1] * turn_count
  starting_numbers[0, starting_numbers.length - 1].each_with_index do |i, n|
    number_to_turn[i] = n
  end
  last_spoken = starting_numbers.last

  (starting_numbers.length...turn_count).each do |turn|
    last_spoken_on_turn = number_to_turn[last_spoken]
    number_to_turn[last_spoken] = turn - 1
    if last_spoken_on_turn < 0
      last_spoken = 0
    else
      last_spoken = turn - last_spoken_on_turn - 1
    end
  end

  last_spoken
end

def main
  p solve(parse_input(INPUT), 2020)
  p solve(parse_input(INPUT), 30_000_000)
end

main if __FILE__ == $0
