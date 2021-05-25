let input = [16; 12; 1; 0; 15; 7; 11]

let solve starting_numbers turn_count =
    let number_to_turn = Array.make (2 * turn_count) (-1) in
    List.iteri (fun i n -> Array.set number_to_turn (2 * n) i) input;
    let last_spoken = List.length starting_numbers |> pred |> List.nth starting_numbers |> ref in
    for turn = List.length starting_numbers to pred turn_count do
        let x = Array.get number_to_turn (2 * !last_spoken) in
        let y = Array.get number_to_turn (2 * !last_spoken + 1) in
        last_spoken := if y == -1 then 0 else x - y;
        let x = Array.get number_to_turn (2 * !last_spoken) in
        Array.set number_to_turn (2 * !last_spoken) turn;
        Array.set number_to_turn (2 * !last_spoken + 1) x
    done;
    !last_spoken

let main =
    solve input 2020 |> print_int;
    print_newline ();
    solve input 30000000 |> print_int;
    print_newline ()
