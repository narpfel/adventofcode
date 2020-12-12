#!/usr/bin/env julia

generation(cells, chairs) = begin
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


main() = begin
    f = open("input")
    chairs = (
        readlines(f)
        |> lines -> reduce(vcat, permutedims.(collect.(lines)))
        |> chars -> chars .== 'L'
    )
    cells = falses(size(chairs))
    while true
        new_cells = generation(cells, chairs)
        if new_cells == cells
            break
        end
        cells = new_cells
    end
    println(sum(cells))
end


if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
