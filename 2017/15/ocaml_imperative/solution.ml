let modulus = 2147483647
let lehmer_rng m a x = (a * x) mod m

let part1 a b =
    let result = ref 0 in
    let a = ref a in
    let b = ref b in
    for _ = 0 to 40_000_000 do
        a := lehmer_rng modulus 16807 !a;
        b := lehmer_rng modulus 48271 !b;
        if (!a land 0xffff) == (!b land 0xffff) then
            result := !result + 1
        else
            ();
    done;
    !result

let part2 a b =
    let result = ref 0 in
    let a = ref a in
    let b = ref b in
    for _ = 0 to 5_000_000 do
        a := lehmer_rng modulus 16807 !a;
        while not (!a mod 4 == 0) do
            a := lehmer_rng modulus 16807 !a
        done;
        b := lehmer_rng modulus 48271 !b;
        while not (!b mod 8 == 0) do
            b := lehmer_rng modulus 48271 !b
        done;
        if (!a land 0xffff) == (!b land 0xffff) then
            result := !result + 1
        else
            ()
    done;
    !result

let () =
    part1 116 299 |> print_int;
    print_newline ();
    part2 116 299 |> print_int;
    print_newline ()
