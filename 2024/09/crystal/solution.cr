struct Empty
  def inspect(io)
    io << "."
  end

  def to_i64
    0
  end
end

EMPTY = Empty.new

def read_input(filename)
  disk_map = File.read(filename).strip.chars.map { |c| c.to_i }

  files = Array(Tuple(Int32, Int32)).new disk_map.size // 2 + 1
  empties = Array(Tuple(Int32, Int32)).new disk_map.size // 2 + 1

  position = 0
  blocks = Array(Int32 | Empty).new disk_map.size * 10
  disk_map
    .each_with_index do |size, i|
      (i.even? ? files : empties) << {position, size}
      position += size
      value = i.even? ? i.to_i // 2 : EMPTY
      size.times { blocks << value }
    end

  {blocks, files, empties}
end

def checksum(blocks)
  blocks.each_with_index.sum { |block, i| i.to_i64 * block.to_i64 }
end

def part_1(blocks)
  checksum = 0_i64
  i = 0
  j = -1
  while i < (blocks.size + j + 1)
    while blocks[j].is_a? Empty
      j -= 1
    end

    if blocks[i].is_a? Empty
      checksum += blocks[j].to_i64 * i.to_i64
      j -= 1
    else
      checksum += blocks[i].to_i64 * i.to_i64
    end
    i += 1
  end

  checksum
end

def fill_next_empty_by_length(next_empty_by_length, absent, empties, start_index)
  start_index.upto(empties.size - 1) do |i|
    _, length = empties[i]
    absent.reject! do |l|
      if l <= length
        next_empty_by_length[l] = i
        true
      else
        false
      end
    end
    return if absent.empty?
  end
end

def part_2(blocks, files, empties)
  next_empty_by_length = [nil.as(Nil | Int32)] * 10
  absent = 0_i64.upto(9_i64).to_a
  fill_next_empty_by_length next_empty_by_length, absent, empties, 0

  files.reverse_each do |pos, length|
    i = next_empty_by_length[length]?
    next if i.nil?

    empty_pos, empty_length = empties[i]

    next if empty_pos >= pos

    absent.clear
    next_empty_by_length.each_with_index do |idx, j|
      if idx == i
        next_empty_by_length[j] = nil
      end
      absent << j if idx.nil? || idx == i
    end

    length.times do |i|
      blocks.swap(empty_pos + i, pos + i)
    end
    empties[i] = {empty_pos + length, empty_length - length}

    fill_next_empty_by_length next_empty_by_length, absent, empties, Math.max(0, i - 1)
  end
  checksum blocks
end

def main
  blocks, files, empties = read_input "input"
  p part_1 blocks
  p part_2 blocks, files, empties
end

main
