#!/usr/bin/env julia

using LinearAlgebra

generation_part1(cells, chairs) = begin
    neighbours = zeros(size(cells))
    for (i, row) in enumerate(eachrow(cells))
        for j in eachindex(row)
            neighbours[i, j] = sum(cells[
                max(i - 1, 1):min(i + 1, size(cells, 1)),
                max(j - 1, 1):min(j + 1, size(row, 1)),
            ]) - cells[i, j]
        end
    end
    (
        (
            cells
            .| (.~cells .& (neighbours .== 0))
        )
        .& .~(cells .& (neighbours .>= 4))
        .& chairs
    )
end


generation_part2(cells, chairs) = begin
    neighbours = zeros(size(cells))
    empty_chairs = chairs .!= cells
    with_chairs = cells .- empty_chairs
    for (i, row) in enumerate(eachrow(cells))
        for j in eachindex(row)
            # Apparently you cannot `reverse` an empty `BitArray`‽ But an empty
            # `Array` is fine?
            lu = diag(reverse(reverse(Array(with_chairs[1:i - 1, 1:j - 1]), dims=1), dims=2))
            ru = diag(reverse(Array(with_chairs[1:i - 1, j + 1:end]), dims=1))
            rd = diag(with_chairs[i + 1:end, j + 1:end])
            ld = diag(reverse(Array(with_chairs[i + 1:end, 1:j - 1]), dims=2))
            neighbours[i, j] = (
                # left
                next_visible_is_alive(reverse(with_chairs[i, 1:j - 1]))
                # left-up
                + next_visible_is_alive(lu)
                # up
                + next_visible_is_alive(reverse(with_chairs[1:i - 1, j]))
                # right-up
                + next_visible_is_alive(ru)
                # right
                + next_visible_is_alive(with_chairs[i, j + 1:end])
                # right-down
                + next_visible_is_alive(rd)
                # down
                + next_visible_is_alive(with_chairs[i + 1:end, j])
                # left-down
                + next_visible_is_alive(ld)
            )
        end
    end
    (
        (
            cells
            .| (.~cells .& (neighbours .== 0))
        )
        .& .~(cells .& (neighbours .>= 5))
        .& chairs
    )
end


slice_square(xss) = xss[1:min(size(xss)...), 1:min(size(xss)...)]


next_visible_is_alive(xs) = (
    xs
    |> xs -> Iterators.dropwhile(x -> x == 0, xs)
    |> xs -> if isempty(xs) false else first(xs) == 1 end
)


find_steady_state(chairs, generation) = begin
    cells = falses(size(chairs))
    while true
        new_cells = generation(cells, chairs)
        if new_cells == cells
            return cells
        end
        cells = new_cells
    end
end


read_input(filename) = open(filename) do io
    (
        eachline(io)
        |> lines -> reduce(vcat, permutedims.(collect.(lines)))
        |> chars -> chars .== 'L'
    )
end


main() = begin
    chairs = read_input("input")
    println(sum(find_steady_state(chairs, generation_part1)))
    println(sum(find_steady_state(chairs, generation_part2)))
end


if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
