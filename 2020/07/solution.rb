#!/usr/bin/env ruby

def parse line
  m = line.match(/^(?<outer_bag_colour>\w+ \w+) bags? contain (?<contained_bags>.+)\n$/)
  outer_bag_colour = m[:outer_bag_colour]
  inner_bag_colours = []
  for inner_bag in m[:contained_bags].split(", ") do
    inner_bag.match(/(?<amount>\d+) (?<colour>\w+ \w+) bags?\.?/) do |m|
      inner_bag_colours.push(m[:colour]) unless m[:amount].to_i == 0
    end
  end
  [outer_bag_colour, inner_bag_colours]
end

def transitively_include? rules, colour, target_colour
  rules[colour].include?(target_colour) ||
    rules[colour].any? { |colour| transitively_include? rules, colour, target_colour }
end

def part1 rules
  rules.each_key.filter { |colour| transitively_include? rules, colour, "shiny gold" }.count
end

def main
  rules = open("input") { |f| f.lines.map { |line| parse(line) } }.to_h
  puts part1(rules)
end

main if __FILE__ == $0
