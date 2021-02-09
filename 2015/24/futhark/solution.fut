let weight: ([]u8 -> u64) = map u64.u8 >-> u64.sum

let quantum_entanglement: ([]u8 -> u64) = map u64.u8 >-> u64.product

let reduced_factorial (from: i64) (to: i64): i64 =
    if from > to then 1 else reduce (*) 1 (from...to)

let factorial: (i64 -> i64) = reduced_factorial 1

let binomial_coefficient (n: i64) (k: i64): i64 =
    let x = i64.max k (n - k)
    let y = i64.min k (n - k)
    in reduced_factorial (x + 1) n / factorial y

let get (xs: []u8) (i: i64) = xs[i]

let get_at indices xs = map (get xs) indices

let combinations (xs: []u8) (l: i64): [][l]u8 =
    let n = length xs
    let pred (i, idx) = idx != i + n - l
    let result_length = binomial_coefficient n l
    let result = replicate result_length (replicate l 0u8) with [0] = take l xs
    let (result, _) =
        loop (result, indices) = (result, iota l) for position in (1..<result_length) do
            let i = loop i = l - 1 while i > 0 && indices[i] == i + n - l do i - 1
            let indices[i] = indices[i] + 1
            let indices =
                if i + 1 > l - 1
                    then indices
                    else loop indices = indices for j in (i + 1...l - 1) do
                              indices with [j] = indices[j - 1] + 1
            let result[position] = get_at indices xs
            in (result, indices)
    in result

let solve (target_weight: u64) (xs: []u8): u64 =
    let lengths = iota (length xs + 1) in
    u64.minimum
        ( map
            ( \l ->
                ( combinations xs l
                |> filter (weight >-> (== target_weight))
                |> map quantum_entanglement
                |> u64.minimum
                )
            ) lengths
        )

let main (input: []u8): (u64, u64) =
    ( solve (weight input / 3) input
    , solve (weight input / 4) input
    )
