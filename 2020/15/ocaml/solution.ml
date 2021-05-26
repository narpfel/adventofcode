module Array = Bigarray.Array1

let input = [16; 12; 1; 0; 15; 7; 11]

let solve starting_numbers turn_count =
    let number_to_turn = Array.create Bigarray.int32 Bigarray.c_layout turn_count in
    Array.fill number_to_turn (-1l);
    List.iteri (fun i n -> Array.set number_to_turn n (Int32.of_int i)) input;
    let last_spoken = List.length starting_numbers |> pred |> List.nth starting_numbers |> ref in
    for turn = List.length starting_numbers to pred turn_count do
        let last_spoken_on_turn = Array.get number_to_turn !last_spoken |> Int32.to_int in
        Array.set number_to_turn !last_spoken (turn |> pred |> Int32.of_int);
        last_spoken := if last_spoken_on_turn < 0 then 0 else turn - last_spoken_on_turn - 1
    done;
    !last_spoken

let main =
    solve input 2020 |> print_int;
    print_newline ();
    solve input 30000000 |> print_int;
    print_newline ()
