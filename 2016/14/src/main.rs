use arraydeque::ArrayDeque;
use generic_array::typenum::U1000;
use generic_array::GenericArray;
use md5::format_digest;
use md5::md5;
use md5::DIGEST_CHAR_LENGTH;

fn has_byte_repetition(s: &[u8], length: usize) -> Option<u8> {
    s.windows(length).find_map(|window| {
        let first_char = window[0];
        if window.iter().all(|&c| c == first_char) {
            Some(first_char)
        }
        else {
            None
        }
    })
}

fn key_stretched(s: &str, count: usize) -> [u8; DIGEST_CHAR_LENGTH] {
    let mut s = s.as_bytes();
    let mut buffer = [0; DIGEST_CHAR_LENGTH];
    for _ in 0..count {
        assert!(s.len() <= DIGEST_CHAR_LENGTH);
        buffer = format_digest(md5(s));
        s = &buffer[..];
    }
    buffer
}

fn otp_indices(salt: &str, key_stretching_count: usize) -> impl Iterator<Item = usize> + '_ {
    type Deque = ArrayDeque<GenericArray<Option<u8>, U1000>, arraydeque::Wrapping>;
    let mut triple_repetitions = Deque::new();
    let mut quintuple_repetitions = Deque::new();

    (0..)
        .map(move |i| format!("{}{}", salt, i))
        .map(move |s| key_stretched(&s, key_stretching_count))
        .enumerate()
        .filter_map(move |(i, digest)| {
            quintuple_repetitions.push_back(has_byte_repetition(&digest, 5));
            triple_repetitions
                .push_back(has_byte_repetition(&digest, 3))
                .flatten()
                .and_then(|c| {
                    if quintuple_repetitions.contains(&Some(c)) {
                        Some(i - 1000)
                    }
                    else {
                        None
                    }
                })
        })
}

fn solve(input: &str, key_stretching_count: usize) -> usize {
    otp_indices(input, key_stretching_count).nth(63).unwrap()
}

const INPUT: &str = "ahsbgdzn";

fn main() {
    println!("{}", solve(INPUT, 1));
    println!("{}", solve(INPUT, 2017));
}
