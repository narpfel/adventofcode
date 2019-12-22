#!/usr/bin/env ruby

class Numeric
  def sign
    self <=> 0
  end
end

class Dimension
  attr_accessor :r, :v

  def initialize(r)
    @r = r
    @v = 0
  end

  def calculate_gravity(other)
    (other.r - @r).sign
  end

  def ==(other)
    @r == other.r && @v == other.v
  end
end

def parse(filename)
  File.open(filename) do |file|
    file.map do |line|
      /<x=(?<x>-?\d+), y=(?<y>-?\d+), z=(?<z>-?\d+)>/ =~ line
      [Dimension.new(x.to_i), Dimension.new(y.to_i), Dimension.new(z.to_i)]
    end
  end.transpose
end

def energy(dimensions)
  dimensions.transpose.sum { |p| p.sum { |x| x.r.abs } * p.sum { |x| x.v.abs }  }
end

def step!(dimensions)
  apply_gravity!(dimensions)
  move!(dimensions)
end

def apply_gravity!(dimensions)
  dimensions.each do |dimension|
    dimension.permutation(2) do |(p1, p2)|
      p1.v += p1.calculate_gravity(p2)
    end
  end
end

def move!(dimensions)
  dimensions.each do |dimension|
    dimension.each do |p|
      p.r += p.v
    end
  end
end

def repeats_after(dimension, initial_state)
  (1..).each do |i|
    step!([dimension])
    if dimension == initial_state
      return i
    end
  end
end

def main
  particles = parse("input")

  1000.times { step!(particles) }
  puts energy(particles)

  initial_state = parse("input")
  particles = parse("input")
  puts particles.zip(initial_state)
    .map { |(dim, initial)| repeats_after(dim, initial) }
    .reduce(1, :lcm)
end

main()
