use std::num::Wrapping;

pub type Word = Wrapping<u32>;

pub const CHUNKSIZE: usize = 512 / 8;
pub const DIGEST_BYTE_COUNT: usize = 16;
pub const DIGEST_CHAR_LENGTH: usize = DIGEST_BYTE_COUNT * 2;

pub const T: [Word; CHUNKSIZE] = ct_python::ct_python! {
    from math import sin
    print("[")
    // TODO: It is apparently impossible to use constants in Python code? Remove hardcoded `64`
    // when this ist possible.
    for i in range(1, 64 + 1):
        val = int(4294967296 * abs(sin(i)))
        print(f "Wrapping({val}),")
    print("]")
};
