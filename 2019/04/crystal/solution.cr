INPUT = "246515-739105"

module Iterator(T)
  def pairwise(&block : T -> U) forall U
    ary = [] of U
    self.each_cons(2, reuse = true) { |(a, b)| ary << yield a, b }
    ary
  end

  def group
    begin
      first_element = self.first
    rescue EmptyError
      [] of Tuple(T, Array(T))
    else
      ary = [{first_element, [first_element]}]
      self.each do |x|
        if x == ary.last[0]
          ary.last[1] << x
        else
          ary << {x, [x]}
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
    password.each_byte.pairwise { |a, b| (a <= b).as(Bool) }.all?
end

def main
  start, end_ = INPUT.split("-").map { |n| n.to_i }
  password_range = start..end_
  valid_passwords = password_range.select { |p| is_valid(p) { |size| size >= 2 } }
  puts(valid_passwords.size)
  puts(valid_passwords.select { |p| is_valid(p) { |size| size == 2 } }.size)
end

main()
