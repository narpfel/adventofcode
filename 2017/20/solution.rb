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

  def at t
    @a.zip(@v, @p).map { |a, v, p| a * t * (t + 1) / 2 + v * t + p }
  end

  def <=> other
    [@a, @v, @p].map(&:manhattan_distance) <=> [other.a, other.v, other.p].map(&:manhattan_distance)
  end

  def collides_with? other, dim = 0
    δa = @a[dim] - other.a[dim]
    δv = @v[dim] - other.v[dim]
    δp = @p[dim] - other.p[dim]

    if δa == 0
      if δv == 0
        if δp == 0
          return self.collides_with?(other, dim + 1)
        else
          return []
        end
      else
        if δp % δv == 0
          return [-δp / δv]
            .filter { |t| t > 0 }
            .filter { |t| self.at(t) == other.at(t) }
        else
          return []
        end
      end
    end

    discriminant = (δa + 2 * δv) ** 2 - 8 * δa * δp
    return [] if discriminant < 0

    discriminant_sqrt = Integer.sqrt(discriminant)
    return [] unless discriminant_sqrt ** 2 == discriminant

    [-(δa + 2 * δv) + discriminant_sqrt, -(δa - 2 * δv) - discriminant_sqrt]
      .uniq
      .filter { |t| t % (2 * δa) == 0 }
      .map { |t| t / (2 * δa) }
      .filter { |t| t > 0 }
      .filter { |t| self.at(t) == other.at(t) }
  end
end

def parse line, value
  line.match(/#{value}=<\s*(-?\d+),\s*(-?\d+),\s*(-?\d+)>/)[1..].map &:to_i
end

def part1 particles
  particles.each_with_index.min_by(&:first).last
end

def part2 particles
  dead = Set[]
  collisions = particles
    .product(particles)
    .reject { |p1, p2| p1.equal? p2 }
    .flat_map { |p1, p2| p1.collides_with?(p2).map { |t| [t, p1, p2] } }
    .group_by(&:first)
    .transform_values { |cs| cs.map { |c| c[1..].flatten.uniq } }
    .to_a
    .sort
    .map(&:last)
    .each do |collision|
      colliding_particles = collision.flatten.reject { |p| dead.include?(p) }
      dead.merge(colliding_particles) unless colliding_particles.length == 1
    end
  particles.length - dead.length
end

def main
  particles = open("input") do |f|
    f.lines.map { |line| Particle.from_line(line) }
  end
  puts part1(particles)
  puts part2(particles)
end

main if __FILE__ == $0
