require "set"

module Enumerable
  def manhattan_distance
    self.map { |x| x.abs }.sum
  end
end

module Math
  def isqrt(n : Int32)
    raise ArgumentError.new "Input must be non-negative integer" if n < 0
    return n if n < 2
    b = n.bit_length
    one = typeof(n).new(1)
    x = one << ((b - 1) >> 1) | n >> ((b >> 1) + 1)
    while (t = n // x) < x
      x = (x + t) >> 1
    end
    x
  end
end

class Particle
  getter :p, :v, :a

  def self.from_line(line)
    self.new(parse(line, "p"), parse(line, "v"), parse(line, "a"))
  end

  def initialize(p : Array(Int32), v : Array(Int32), a : Array(Int32))
    @p = p
    @v = v
    @a = a
  end

  def at(t)
    @a.zip(@v, @p).map { |a, v, p| a * t * (t + 1) // 2 + v * t + p }
  end

  def <=>(other)
    [@a, @v, @p].map { |xs| xs.manhattan_distance } \
      <=> [other.a, other.v, other.p].map { |xs| xs.manhattan_distance }
  end

  def collides_with?(other, dim = 0)
    δa = @a[dim] - other.a[dim]
    δv = @v[dim] - other.v[dim]
    δp = @p[dim] - other.p[dim]

    if δa == 0
      if δv == 0
        if δp == 0
          return self.collides_with?(other, dim + 1)
        else
          return [] of Int32
        end
      else
        if δp % δv == 0
          return [-δp // δv]
            .select { |t| t > 0 }
            .select { |t| self.at(t) == other.at(t) }
        else
          return [] of Int32
        end
      end
    end

    discriminant = (δa + 2 * δv) ** 2 - 8 * δa * δp
    return [] of Int32 if discriminant < 0

    discriminant_sqrt = Math.isqrt(discriminant)
    return [] of Int32 unless discriminant_sqrt ** 2 == discriminant

    [-(δa + 2 * δv) + discriminant_sqrt, -(δa - 2 * δv) - discriminant_sqrt]
      .uniq
      .select { |t| t % (2 * δa) == 0 }
      .map { |t| t // (2 * δa) }
      .select { |t| t > 0 }
      .select { |t| self.at(t) == other.at(t) }
  end
end

def parse(line, value)
  match = line.match(/#{value}=<\s*(-?\d+),\s*(-?\d+),\s*(-?\d+)>/).not_nil!
  (1...match.size).map { |i| match[i].to_i }
end

def part1(particles)
  particles.map_with_index { |i, p| {i, p} }.min_by { |(i, p)| i }.last
end

def part2(particles)
  dead = Set(Particle).new()
  collisions = (0...particles.size)
    .flat_map { |i| (0...particles.size).map { |j| {particles[i], particles[j]} } }
    .reject! { |p1, p2| p1.same? p2 }
    .flat_map { |p1, p2| p1.collides_with?(p2).map { |t| {t, p1, p2} } }
    .group_by { |c| c.first }
    .transform_values { |cs| cs.map { |c| [c[1], c[2]].flatten.uniq } }
    .to_a
    .sort
    .map { |ary| ary.last }
    .each do |collision|
      colliding_particles = collision.flatten.reject { |p| dead.includes?(p) }
      dead.concat(colliding_particles) unless colliding_particles.size == 1
    end
  particles.size - dead.size
end

def main
  particles = File.open("input") do |f|
    f.each_line.map { |line| Particle.from_line(line) }.to_a
  end
  puts part1(particles)
  puts part2(particles)
end

main
