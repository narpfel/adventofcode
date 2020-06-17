#![feature(core_intrinsics)]

use std::intrinsics::assume;

use std::{
    io::Cursor,
    num::Wrapping,
};

use std::borrow::Cow;

use arraydeque::ArrayDeque;
use generic_array::{
    typenum::U1000,
    GenericArray,
};

use byteorder::{
    ByteOrder,
    LittleEndian,
    ReadBytesExt,
    WriteBytesExt,
};

mod constants;
use constants::*;

fn pad(bytes: &[u8], total_length: Wrapping<u64>) -> Vec<u8> {
    let len = bytes.len();
    if len > CHUNKSIZE {
        panic!("Invalid chunk length: {} > {}", len, CHUNKSIZE);
    }

    let number_of_chunks = if len > CHUNKSIZE - 9 { 2 } else { 1 };

    let mut buffer = Vec::with_capacity(number_of_chunks * CHUNKSIZE);

    buffer.extend_from_slice(bytes);
    buffer.push(0b1000_0000);
    buffer.resize(number_of_chunks * CHUNKSIZE - 8, 0);
    buffer
        .write_u64::<LittleEndian>((total_length * Wrapping(8)).0)
        .unwrap_or_else(|_| unreachable!());
    buffer
}

struct Chunks<'a> {
    chunk_count: Wrapping<u64>,
    chunks: std::iter::Peekable<std::slice::Chunks<'a, u8>>,
    last_chunk: Option<Cow<'a, [u8]>>,
}

impl<'a> Iterator for Chunks<'a> {
    type Item = Cow<'a, [u8]>;

    fn next(&mut self) -> Option<Self::Item> {
        self.chunks
            .next()
            .and_then(|chunk| {
                if self.chunks.peek().is_some() {
                    self.chunk_count += Wrapping(1);
                    return Some(chunk.into());
                }
                let p = pad(
                    chunk,
                    Wrapping(CHUNKSIZE as u64) * self.chunk_count + Wrapping(chunk.len() as u64),
                );
                let mut padded_chunks = p.chunks(CHUNKSIZE).map(|c| Cow::Owned(c.into()));
                let first = padded_chunks.next();
                self.last_chunk = padded_chunks.next();
                first
            })
            .or_else(|| self.last_chunk.take())
    }
}

fn chunks(bytes: &[u8]) -> Chunks {
    let last_chunk = if bytes.is_empty() {
        let mut padded_empty_bytes = Vec::with_capacity(CHUNKSIZE);
        padded_empty_bytes.push(0b1000_0000);
        padded_empty_bytes.resize(CHUNKSIZE - 8, 0);
        padded_empty_bytes
            .write_u64::<LittleEndian>(0)
            .unwrap_or_else(|_| unreachable!());
        Some(padded_empty_bytes.into())
    }
    else {
        None
    };

    Chunks {
        chunk_count: Wrapping(0),
        chunks: bytes.chunks(CHUNKSIZE).peekable(),
        last_chunk,
    }
}

fn read_word(buffer: &[u8]) -> Word {
    Wrapping(LittleEndian::read_u32(buffer))
}

fn md5(bytes: &[u8]) -> [u8; DIGEST_BYTE_COUNT] {
    // Single-letter variable names match the names given in the MD5 RFC (RFC 1321),
    // see https://www.ietf.org/rfc/rfc1321.txt
    #![allow(clippy::many_single_char_names)]

    let mut a = read_word(&[0x01, 0x23, 0x45, 0x67]);
    let mut b = read_word(&[0x89, 0xab, 0xcd, 0xef]);
    let mut c = read_word(&[0xfe, 0xdc, 0xba, 0x98]);
    let mut d = read_word(&[0x76, 0x54, 0x32, 0x10]);

    let f = |x: Word, y, z| (x & y) | (!x & z);
    let g = |x, y, z: Word| (x & z) | (y & !z);
    let h = |x, y, z| x ^ y ^ z;
    let i = |x, y, z: Word| y ^ (x | !z);

    let rotate = |x, s| (x << s) | (x >> (32 - s));

    let index = |stride, shift| move |i: usize| (stride * i + shift) % 16;

    for chunk in chunks(bytes) {
        unsafe {
            assume(chunk.as_ptr() as usize % CHUNKSIZE == 0)
        };
        unsafe {
            assume(chunk.len() == CHUNKSIZE)
        };
        let aa = a;
        let bb = b;
        let cc = c;
        let dd = d;
        let mut t_index = 0;

        let mut buffer = [Wrapping(0u32); CHUNKSIZE / 4];
        let mut cursor = Cursor::new(chunk);
        for word in buffer.iter_mut() {
            *word = Wrapping(
                cursor
                    .read_u32::<LittleEndian>()
                    .unwrap_or_else(|_| unreachable!()),
            );
        }

        struct Round<Index: Fn(usize) -> usize> {
            round: fn(Word, Word, Word) -> Word,
            index: Index,
            s_cycle: [usize; 4],
        }

        let md5_rounds: [Round<_>; 4] = [
            Round {
                round: f,
                index: index(1, 0),
                s_cycle: [7, 12, 17, 22],
            },
            Round {
                round: g,
                index: index(5, 1),
                s_cycle: [5, 9, 14, 20],
            },
            Round {
                round: h,
                index: index(3, 5),
                s_cycle: [4, 11, 16, 23],
            },
            Round {
                round: i,
                index: index(7, 0),
                s_cycle: [6, 10, 15, 21],
            },
        ];

        for Round { round, index, s_cycle } in &md5_rounds {
            for (k, &s) in (0..CHUNKSIZE / 4).map(index).zip(s_cycle.iter().cycle()) {
                let tmp = d;
                d = c;
                c = b;
                b += rotate(a + round(c, d, tmp) + buffer[k] + T[t_index], s);
                a = tmp;
                t_index += 1;
            }
        }

        a += aa;
        b += bb;
        c += cc;
        d += dd;
    }

    let mut result = [0; DIGEST_BYTE_COUNT];
    let mut cursor = Cursor::new(&mut result[..]);
    for x in &[a, b, c, d] {
        cursor
            .write_u32::<LittleEndian>(x.0)
            .unwrap_or_else(|_| unreachable!());
    }
    result
}

fn format_digest(digest: [u8; DIGEST_BYTE_COUNT]) -> [u8; DIGEST_CHAR_LENGTH] {
    const HEX_DIGITS: &[u8] = b"0123456789abcdef";

    let mut result = [0; DIGEST_CHAR_LENGTH];
    digest.iter().enumerate().for_each(|(i, byte)| {
        let upper_nibble = byte >> 4;
        let lower_nibble = byte & 0xf;
        result[2 * i] = HEX_DIGITS[upper_nibble as usize];
        result[2 * i + 1] = HEX_DIGITS[lower_nibble as usize];
    });
    result
}

fn has_byte_repetition(s: &[u8], length: usize) -> Option<u8> {
    s.windows(length)
        .filter_map(|window| {
            let first_char = window[0];
            if window.iter().all(|&c| c == first_char) {
                Some(first_char)
            }
            else {
                None
            }
        })
        .next()
}

fn key_stretched(s: &str, count: usize) -> [u8; DIGEST_CHAR_LENGTH] {
    let mut s = s.as_bytes();
    let mut buffer = [0; DIGEST_CHAR_LENGTH];
    for _ in 0..count {
        buffer = format_digest(md5(s));
        s = &buffer[..];
    }
    buffer
}

fn otp_indices<'a>(salt: &'a str, key_stretching_count: usize) -> impl Iterator<Item = usize> + 'a {
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
