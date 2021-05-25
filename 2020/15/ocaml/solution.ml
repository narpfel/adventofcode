let input = [16; 12; 1; 0; 15; 7; 11]

let solve starting_numbers turn_count =
    let number_to_turn = Array.make turn_count (-1) in
    List.iteri (fun i n -> Array.set number_to_turn n i) input;
    let last_spoken = List.length starting_numbers |> pred |> List.nth starting_numbers |> ref in
    for turn = List.length starting_numbers to pred turn_count do
        let last_spoken_on_turn = Array.get number_to_turn !last_spoken in
        Array.set number_to_turn !last_spoken (pred turn);
        last_spoken := if last_spoken_on_turn < 0 then 0 else turn - last_spoken_on_turn - 1
    done;
    !last_spoken

let main =
    solve input 2020 |> print_int;
    print_newline ();
    solve input 30000000 |> print_int;
    print_newline ()
