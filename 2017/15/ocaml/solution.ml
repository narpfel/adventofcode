let modulus = 2147483647
let lehmer_rng m a x = (a * x) mod m
let lsbs n = (n land 0xffff)

let generator a x = Seq.iterate (lehmer_rng modulus a) x |> Seq.drop 1

let solve length a pa b pb
    = Seq.map2 (fun x y -> (lsbs x) == (lsbs y))
        (generator 16807 a |> Seq.filter pa)
        (generator 48271 b |> Seq.filter pb)
    |> Seq.take length
    |> Seq.filter Fun.id
    |> Seq.length

let part1 a b = solve 40_000_000 a (Fun.const true) b (Fun.const true)

let is_multiple_of a b = (b mod a) == 0
let part2 a b = solve 5_000_000 a (is_multiple_of 4) b (is_multiple_of 8)

let () =
    part1 116 299 |> print_int;
    print_newline ();
    part2 116 299 |> print_int;
    print_newline ()
