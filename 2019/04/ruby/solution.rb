#!/usr/bin/env ruby

INPUT = "246515-739105"

class Enumerator
  def pairwise
    ary = []
    self.each_cons(2) { |a, b| ary << (yield a, b) }
    ary
  end

  def group
    begin
      first_element = self.first
    rescue EmptyError
      []
    else
      ary = [[first_element, [first_element]]]
      self.drop(1).each do |x|
        if x == ary.last[0]
          ary.last[1] << x
        else
          ary << [x, [x]]
        end
      end
      ary
    end
  end
end

def is_valid(password)
  password = password.to_s
  password.size == 6 &&
    password.each_byte.group.any? { |(_, group)| yield group.size } &&
    password.each_byte.pairwise { |a, b| a <= b }.all?
end

def main
  start, end_ = INPUT.split("-").map { |n| n.to_i }
  password_range = start..end_
  valid_passwords = password_range.select { |p| is_valid(p) { |size| size >= 2 } }
  puts(valid_passwords.size)
  puts(valid_passwords.select { |p| is_valid(p) { |size| size == 2 } }.size)
end

main()
