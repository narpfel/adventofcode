#!/usr/bin/env ruby

require 'set'

module Enumerable
  def manhattan_distance
    self.map(&:abs).sum
  end
end

class Particle
  attr_reader :p, :v, :a

  def self.from_line line
    self.new(*["p", "v", "a"].map { |value| parse(line, value) })
  end

  def initialize p, v, a
    @p = p
    @v = v
    @a = a
  end

  def move!
    @v = @v.zip(@a).map { |v, a| v + a }
    @p = @p.zip(@v).map { |p, v| p + v }
  end

  def <=> other
    [@a, @v, @p].map(&:manhattan_distance) <=> [other.a, other.v, other.p].map(&:manhattan_distance)
  end
end

def parse line, value
  line.match(/#{value}=<\s*(-?\d+),\s*(-?\d+),\s*(-?\d+)>/)[1..].map &:to_i
end

def part1 particles
  particles.each_with_index.min_by(&:first).last
end

def simulate_step particles
  particles.each &:move!
  particles.group_by(&:p).values.reject { |ps| ps.length > 1 }.flatten
end

def part2 particles
  # FIXME: This assumes that 100 steps are enough to reach a steady state.
  # For my input, all collisions are resolved after 39 steps, so this seems
  # like an acceptable safety margin. A more elegant solution would be to
  # calculate the necessary amount of steps beforehand.
  100.times do
    particles = simulate_step(particles)
  end
  particles.length
end

def main
  particles = open("input") do |f|
    f.lines.map { |line| Particle.from_line(line) }
  end
  puts part1(particles)
  puts part2(particles)
end

main if __FILE__ == $0
