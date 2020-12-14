#!/usr/bin/env julia

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
            neighbours[i, j] = (
                # left
                next_visible_is_alive(with_chairs[i, j - 1:-1:1])
                # left-up
                + (diagonal_for(with_chairs, i - 1:-1:1, j - 1:-1:1) |> next_visible_is_alive)
                # up
                + next_visible_is_alive(with_chairs[i - 1:-1:1, j])
                # right-up
                + (diagonal_for(with_chairs, i - 1:-1:1, j + 1:size(with_chairs, 2)) |> next_visible_is_alive)
                # right
                + next_visible_is_alive(with_chairs[i, j + 1:end])
                # right-down
                + (diagonal_for(with_chairs, i + 1:size(with_chairs, 1), j + 1:size(with_chairs, 2)) |> next_visible_is_alive)
                # down
                + next_visible_is_alive(with_chairs[i + 1:end, j])
                # left-down
                + (diagonal_for(with_chairs, i + 1:size(with_chairs, 1), j - 1:-1:1) |> next_visible_is_alive)
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


next_visible_is_alive(xs) = (
    xs
    |> xs -> Iterators.dropwhile(x -> x == 0, xs)
    |> xs -> if isempty(xs) false else first(xs) == 1 end
)


diagonal_for(xss, is, js) = (
    Iterators.zip(is, js)
    |> ixs -> Iterators.map(ix -> xss[ix...], ixs)
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
