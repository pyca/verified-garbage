//! Checks of the stream-like modes (CFB and OFB) on their published
//! vectors, each also truncated and split, since a mode's vectors are
//! whole messages of a few blocks and the code has paths for a partial last
//! segment and for a message continued in pieces. Nothing here computes a
//! cipher: every expected output is a prefix of the vector's, and every
//! chaining value one of its blocks, or the keystream block `P ⊕ C` that a
//! whole block of the vector gives.

/// Whether a mode's chaining value after a partial segment is the keystream
/// block (CFB, OFB) and after a whole block the ciphertext block (CFB) or
/// the keystream block (OFB).
#[derive(Clone, Copy)]
pub enum Feedback {
    /// CFB: the next input block is the ciphertext block.
    Ciphertext,
    /// OFB: the next input block is the output block.
    Output,
}

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

/// The chaining value after the first `len` bytes of a message from `iv`
/// whose plaintext and ciphertext are `p` and `c` (one of them encrypted,
/// the other decrypted, so `p ⊕ c` is the keystream), or `None` if the
/// vector does not give it: a keystream block of which it has only part.
fn chain_after<const B: usize>(
    feedback: Feedback,
    iv: [u8; B],
    p: &[u8],
    c: &[u8],
    len: usize,
) -> Option<[u8; B]> {
    if len == 0 {
        return Some(iv);
    }
    let whole = len.is_multiple_of(B);
    let block = (len - 1) / B;
    let range = B * block..B * (block + 1);
    if range.end > p.len() {
        return None;
    }
    if whole && matches!(feedback, Feedback::Ciphertext) {
        return Some(c[range].try_into().unwrap());
    }
    Some(core::array::from_fn(|i| {
        p[range.start + i] ^ c[range.start + i]
    }))
}

/// `crypt(iv, buffer)` takes `input` to `output` from `iv`: on the vector
/// truncated to each of [`lengths`], whole, and on the whole vector split
/// into two calls at every block, leaving the chaining value that the
/// vector gives (`chain_after`, where it gives one); `p` and `c` are the
/// vector's plaintext and ciphertext.
pub fn check<const B: usize>(
    feedback: Feedback,
    iv: [u8; B],
    (p, c): (&[u8], &[u8]),
    (input, output): (&[u8], &[u8]),
    crypt: &dyn Fn(&mut [u8; B], &mut [u8]),
) {
    for len in lengths(input.len(), B) {
        let mut chain = iv;
        let mut buffer = input[..len].to_vec();
        crypt(&mut chain, &mut buffer);
        assert_eq!(buffer, output[..len], "length {len}");
        if let Some(after) = chain_after(feedback, iv, p, c, len) {
            assert_eq!(chain, after, "length {len}");
        }
    }
    let after = chain_after(feedback, iv, p, c, input.len());
    for offset in (0..=input.len()).step_by(B) {
        let mut chain = iv;
        let mut buffer = input.to_vec();
        let (a, b) = buffer.split_at_mut(offset);
        crypt(&mut chain, a);
        crypt(&mut chain, b);
        assert_eq!(buffer, output, "split at {offset}");
        if let Some(after) = after {
            assert_eq!(chain, after, "split at {offset}");
        }
    }
}

/// `crypt(iv, buffer)` takes `input` to `output` from `iv` in place, with
/// the buffer and the IV at every offset below 16 in larger buffers whose
/// other bytes it leaves as they were; `after` is the chaining value it
/// must leave.
pub fn check_unaligned<const B: usize>(
    iv: [u8; B],
    (input, output): (&[u8], &[u8]),
    after: [u8; B],
    crypt: &dyn Fn(&mut [u8; B], &mut [u8]),
) {
    let len = input.len();
    for offset in 0..16 {
        let mut buffer = vec![0xa5; len + 32];
        buffer[offset..offset + len].copy_from_slice(input);
        let mut chain = vec![0xa5; B + 32];
        chain[offset..offset + B].copy_from_slice(&iv);
        crypt(
            (&mut chain[offset..offset + B]).try_into().unwrap(),
            &mut buffer[offset..offset + len],
        );
        assert_eq!(&buffer[offset..offset + len], output, "offset {offset}");
        assert_eq!(chain[offset..offset + B], after, "offset {offset}");
        assert!(crate::bytes::all_equal(&buffer[..offset], 0xa5));
        assert!(crate::bytes::all_equal(&buffer[offset + len..], 0xa5));
        assert!(crate::bytes::all_equal(&chain[..offset], 0xa5));
        assert!(crate::bytes::all_equal(&chain[offset + B..], 0xa5));
    }
}

/// CTR's counter, with no cipher computed here: `apply(ctr, buffer)` on
/// `blocks` zero blocks from the counter block `start` gives as block `j`
/// what it gives on one block from `start + j` (modulo 2¹²⁸, as
/// `crate::bytes::counter_add` counts), and leaves `start + blocks`; and
/// it gives the same keystream on a buffer at any offset below 16, leaving
/// the bytes around it as they were.
pub fn check_counter(start: [u8; 16], blocks: usize, apply: &dyn Fn(&mut [u8; 16], &mut [u8])) {
    let mut ctr = start;
    let mut stream = vec![0; 16 * blocks];
    apply(&mut ctr, &mut stream);
    assert_eq!(ctr, crate::bytes::counter_add(&start, blocks));
    for (j, block) in stream.chunks(16).enumerate() {
        let mut ctr = crate::bytes::counter_add(&start, j);
        let mut one = [0; 16];
        apply(&mut ctr, &mut one);
        assert_eq!(one, block, "block {j}");
    }
    let zeros = vec![0; stream.len()];
    check_unaligned(start, (&zeros, &stream), ctr, apply);
}
