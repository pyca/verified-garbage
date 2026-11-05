//! Checks of the stream-like modes (CFB, OFB and CTR) on their published
//! vectors, each also truncated and split, since a mode's vectors are
//! whole messages of a few blocks and the code has paths for a partial last
//! segment and for a message continued in pieces. Nothing here computes a
//! cipher: every expected output is a prefix of the vector's, or a block of
//! keystream that the mode itself gives.
//!
//! A mode is a type `T` that `new(iv)` starts from an IV (or initial counter
//! block), `apply(&mut t, buffer)` continues on the next whole blocks of the
//! message (refusing any other length), and `finish(t, buffer)` ends with
//! the rest of the message, of any length, all in place.

/// The lengths a vector of `len` bytes is truncated to: every length up to
/// two blocks, every whole number of blocks, and the vector's own length and
/// the one before it.
fn lengths(len: usize, block: usize) -> Vec<usize> {
    let mut lens: Vec<usize> = (0..=len.min(2 * block)).collect();
    lens.extend((0..=len).step_by(block));
    lens.extend([len.saturating_sub(1), len]);
    lens.sort_unstable();
    lens.dedup();
    lens
}

/// The mode takes `input` to `output` from `iv`:
///
/// * on the vector truncated to each of [`lengths`], ended in one call (or,
///   for a whole number of blocks, continued in one);
/// * on the whole vector in two calls, the first continuing on the whole
///   blocks before each block boundary (after an empty one) and the second
///   ending; and a block at a time, then ending with what is left;
/// * after a call on a piece that is not a whole number of blocks, which it
///   refuses, changing neither the piece nor the state, at every length.
pub fn check<T, E: core::fmt::Debug, const B: usize>(
    iv: [u8; B],
    (input, output): (&[u8], &[u8]),
    new: &dyn Fn(&[u8; B]) -> T,
    apply: fn(&mut T, &mut [u8]) -> Result<(), E>,
    finish: fn(T, &mut [u8]),
) {
    for len in lengths(input.len(), B) {
        let mut buffer = input[..len].to_vec();
        finish(new(&iv), &mut buffer);
        assert_eq!(buffer, output[..len], "length {len}");
        if len.is_multiple_of(B) {
            let mut buffer = input[..len].to_vec();
            apply(&mut new(&iv), &mut buffer).unwrap();
            assert_eq!(buffer, output[..len], "length {len}");
        }
    }
    let len = input.len();
    for split in (0..=len).step_by(B) {
        let mut buffer = input.to_vec();
        let mut t = new(&iv);
        apply(&mut t, &mut []).unwrap();
        let (a, b) = buffer.split_at_mut(split);
        apply(&mut t, a).unwrap();
        finish(t, b);
        assert_eq!(buffer, output, "split at {split}");
    }
    let mut buffer = input.to_vec();
    let mut t = new(&iv);
    let whole = len / B * B;
    for block in buffer[..whole].chunks_mut(B) {
        apply(&mut t, block).unwrap();
    }
    finish(t, &mut buffer[whole..]);
    assert_eq!(buffer, output, "a block at a time");
    for split in 0..=len {
        if split.is_multiple_of(B) {
            continue;
        }
        let mut buffer = input.to_vec();
        let mut t = new(&iv);
        assert!(apply(&mut t, &mut buffer[..split]).is_err());
        assert_eq!(buffer, input, "refused at {split}");
        finish(t, &mut buffer);
        assert_eq!(buffer, output, "after a refusal at {split}");
    }
}

/// The mode, ending a message from `iv` in one call, takes `input` to
/// `output` in place, with the buffer at every offset below 16 in a larger
/// buffer whose other bytes it leaves as they were.
pub fn check_unaligned<T, const B: usize>(
    iv: [u8; B],
    (input, output): (&[u8], &[u8]),
    new: &dyn Fn(&[u8; B]) -> T,
    finish: fn(T, &mut [u8]),
) {
    let len = input.len();
    for offset in 0..16 {
        let mut buffer = vec![0xa5; len + 32];
        buffer[offset..offset + len].copy_from_slice(input);
        finish(new(&iv), &mut buffer[offset..offset + len]);
        assert_eq!(&buffer[offset..offset + len], output, "offset {offset}");
        assert!(crate::bytes::all_equal(&buffer[..offset], 0xa5));
        assert!(crate::bytes::all_equal(&buffer[offset + len..], 0xa5));
    }
}

/// CTR's counter, with no cipher computed here: CTR on `blocks` zero blocks
/// from the counter block `start` gives as block `j` what it gives on one
/// block from `start + j` (modulo 2¹²⁸, as `crate::bytes::counter_add`
/// counts), and continues with what it gives from `start + blocks`; and it
/// gives the same keystream on a buffer at any offset below 16, leaving the
/// bytes around it as they were.
pub fn check_counter<T, E: core::fmt::Debug>(
    start: [u8; 16],
    blocks: usize,
    new: &dyn Fn(&[u8; 16]) -> T,
    apply: fn(&mut T, &mut [u8]) -> Result<(), E>,
    finish: fn(T, &mut [u8]),
) {
    let mut ctr = new(&start);
    let mut stream = vec![0; 16 * blocks];
    apply(&mut ctr, &mut stream).unwrap();
    for (j, block) in stream.chunks(16).enumerate() {
        let mut one = [0; 16];
        finish(new(&crate::bytes::counter_add(&start, j)), &mut one);
        assert_eq!(one, block, "block {j}");
    }
    let mut next = [0; 16];
    finish(ctr, &mut next);
    let mut expected = [0; 16];
    finish(
        new(&crate::bytes::counter_add(&start, blocks)),
        &mut expected,
    );
    assert_eq!(next, expected);
    let zeros = vec![0; stream.len()];
    check_unaligned(start, (&zeros, &stream), new, finish);
}
