#!/usr/bin/env lua5.4

INPUT = "16,12,1,0,15,7,11"

function parse_input(starting_numbers)
    local numbers = {}
    for s in starting_numbers:gmatch("([^,]+)") do
        table.insert(numbers, tonumber(s))
    end
    return numbers
end

function solve(starting_numbers, turn_count)
    local number_to_turn = {}
    for i = 1, turn_count do
        table.insert(number_to_turn, -1)
    end

    for i = 1, #starting_numbers - 1 do
        number_to_turn[starting_numbers[i] + 1] = i - 1
    end
    local last_spoken = starting_numbers[#starting_numbers]

    for turn = #starting_numbers, turn_count - 1 do
        local last_spoken_on_turn = number_to_turn[last_spoken + 1]
        number_to_turn[last_spoken + 1] = turn - 1
        if last_spoken_on_turn < 0 then
            last_spoken = 0
        else
            last_spoken = turn - last_spoken_on_turn - 1
        end
    end

    return last_spoken
end

print(solve(parse_input(INPUT), 2020))
print(solve(parse_input(INPUT), 30000000))
