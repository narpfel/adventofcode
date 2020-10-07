#!/usr/bin/env ruby

def manhattan_distance xs
  xs.map(&:abs).sum
end

def parse line, value
  line.match(/#{value}=<\s*(-?\d+),\s*(-?\d+),\s*(-?\d+)>/)[1..].map &:to_i
end

def part1 particles
  particles.map { |p|
    p.map { |xs| manhattan_distance(xs) }
  }.each_with_index.min_by(&:first).last
end

def main
  particles = open("input") do |f|
    f.lines.map do |line|
      ["a", "v", "p"].map { |value| parse(line, value) }
    end
  end
  puts part1(particles)
end

main if __FILE__ == $0
