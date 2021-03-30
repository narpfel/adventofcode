use std::iter::once;

const INPUT_DIGITS: [u8; 6] = [2, 9, 0, 4, 3, 1];
const INPUT: usize = {
    let mut input = 0;
    let mut i = 0;
    // TODO: Iterators and `for` not allowed in const evaluation.
    loop {
        input += INPUT_DIGITS[i] as usize;
        if i == INPUT_DIGITS.len() - 1 {
            break;
        }
        input *= 10;
        i += 1;
    }
    input
};

fn next_scores(scores: &[u8], elves: (usize, usize)) -> impl Iterator<Item = u8> {
    let sum = scores[elves.0] + scores[elves.1];
    once(if sum >= 10 { Some(1) } else { None })
        .chain(once(if sum >= 10 { Some(sum - 10) } else { Some(sum) }))
        .flatten()
}

fn main() {
    let mut scores = vec![3, 7];
    scores.reserve(INPUT + 10);
    let mut elves = (0, 1);
    while scores.len() < INPUT + 10
        || (!scores.ends_with(&INPUT_DIGITS)
            && !scores[..scores.len() - 1].ends_with(&INPUT_DIGITS))
    {
        scores.extend(next_scores(&scores, elves));
        elves.0 = (1 + elves.0 + scores[elves.0] as usize) % scores.len();
        elves.1 = (1 + elves.1 + scores[elves.1] as usize) % scores.len();
    }
    println!(
        "{}",
        &scores[INPUT..INPUT + 10]
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("")
    );
    println!(
        "{}",
        // We have to search the scores of all recipes because `INPUT_DIGITS` could be present
        // in the scores generated for part 1.
        scores
            .windows(INPUT_DIGITS.len())
            .position(|xs| xs == INPUT_DIGITS)
            .unwrap()
    );
}
