#![feature(array_chunks)]

use std::{
    io::{
        Cursor,
        Seek,
        SeekFrom,
        Write,
    },
    num::Wrapping,
};

use byteorder::{
    ByteOrder,
    LittleEndian,
    ReadBytesExt,
    WriteBytesExt,
};

mod constants;
pub use constants::DIGEST_CHAR_LENGTH;
use constants::*;

fn pad<'a>(
    bytes: &'a [u8],
    total_length: Wrapping<u64>,
    buffer: &'a mut [u8; 2 * CHUNKSIZE],
) -> std::io::Result<&'a [u8]> {
    let len = bytes.len();
    if len > CHUNKSIZE {
        panic!("Invalid chunk length: {} > {}", len, CHUNKSIZE);
    }

    let number_of_chunks = if len > CHUNKSIZE - 9 { 2 } else { 1 };

    let buffer = if number_of_chunks == 1 {
        &mut buffer[..CHUNKSIZE]
    }
    else {
        buffer
    };

    let mut cursor = Cursor::new(buffer);
    cursor.write_all(bytes)?;
    cursor.write_u8(0b1000_0000)?;
    cursor.seek(SeekFrom::End(-8))?;
    cursor.write_u64::<LittleEndian>((total_length * Wrapping(8)).0)?;
    Ok(cursor.into_inner())
}

struct Chunks<'a> {
    chunk_count: Wrapping<u64>,
    chunks: std::slice::ArrayChunks<'a, u8, CHUNKSIZE>,
    last_chunk: Option<&'a [u8; CHUNKSIZE]>,
    buffer: Option<&'a mut [u8; 2 * CHUNKSIZE]>,
}

impl<'a> Iterator for Chunks<'a> {
    type Item = &'a [u8; CHUNKSIZE];

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        self.chunks
            .next()
            .map(|chunk| {
                self.chunk_count += Wrapping(1);
                chunk
            })
            .or_else(|| {
                let buffer = self.buffer.take()?;
                let chunk = self.chunks.remainder();
                let mut padded_chunks = pad(
                    chunk,
                    Wrapping(CHUNKSIZE as u64) * self.chunk_count + Wrapping(chunk.len() as u64),
                    buffer,
                )
                .ok()?
                .array_chunks();
                let first_chunk = padded_chunks.next();
                self.last_chunk = padded_chunks.next();
                first_chunk
            })
            .or_else(|| self.last_chunk.take())
    }
}

fn chunks<'a>(bytes: &'a [u8], buffer: &'a mut [u8; 2 * CHUNKSIZE]) -> Chunks<'a> {
    Chunks {
        chunk_count: Wrapping(0),
        chunks: bytes.array_chunks(),
        last_chunk: None,
        buffer: Some(buffer),
    }
}

fn read_word(buffer: &[u8]) -> Word {
    Wrapping(LittleEndian::read_u32(buffer))
}

#[inline]
pub fn md5(bytes: &[u8]) -> [u8; DIGEST_BYTE_COUNT] {
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

    for chunk in chunks(bytes, &mut [0; 2 * CHUNKSIZE]) {
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

#[inline]
pub fn format_digest(digest: [u8; DIGEST_BYTE_COUNT]) -> [u8; DIGEST_CHAR_LENGTH] {
    const HEX_DIGITS: &[u8] = b"0123456789abcdef";

    let mut result = [0; DIGEST_CHAR_LENGTH];
    digest.into_iter().enumerate().for_each(|(i, byte)| {
        let upper_nibble = byte >> 4;
        let lower_nibble = byte & 0xf;
        result[2 * i] = HEX_DIGITS[upper_nibble as usize];
        result[2 * i + 1] = HEX_DIGITS[lower_nibble as usize];
    });
    result
}
