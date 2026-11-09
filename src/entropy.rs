//! Supplying random bytes to verified code that asks for them.

#![cfg(all(
    any(
        target_arch = "x86",
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "arm",
        all(target_arch = "powerpc64", target_endian = "little"),
        target_arch = "riscv64"
    ),
    feature = "alloc"
))]

use crate::zeroize::zeroize;
use alloc::{vec, vec::Vec};

/// A random tape, wiped when dropped: it holds the secrets drawn from it.
struct Tape(Vec<u8>);

impl Drop for Tape {
    fn drop(&mut self) {
        zeroize(&mut self.0);
    }
}

/// What a verified operation did with its tape.
pub(crate) enum Step {
    /// It finished.
    Done,
    /// It failed, for a reason more random bytes cannot fix (an invalid
    /// input, or its limit of attempts).
    Failed,
    /// It needs more random bytes: discard the first `used` bytes of the
    /// tape, keep the rest and extend it to `requested` bytes.
    More {
        /// The bytes of the tape it consumed.
        used: usize,
        /// The length of the next tape.
        requested: usize,
    },
}

/// Why [`serve`] stopped without the operation finishing.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Stop<E> {
    /// The operation failed ([`Step::Failed`]).
    Failed,
    /// Filling a tape failed, with this error.
    Fill(E),
}

/// Run `step` on a tape of `requested` random bytes from `fill`, and again
/// on each tape it asks for, until it finishes or fails. `fill` is never
/// asked for zero bytes, so an operation that fails before it needs any
/// (`requested` is 0) draws none.
///
/// A verified operation may keep secrets in the tape, and an unfinished one
/// is run again on the tape's preserved suffix, so each tape is a new
/// allocation and the one it replaces is wiped.
pub(crate) fn serve<E>(
    requested: usize,
    mut fill: impl FnMut(&mut [u8]) -> Result<(), E>,
    mut step: impl FnMut(&[u8]) -> Step,
) -> Result<(), Stop<E>> {
    let mut tape = Tape(vec![0; requested]);
    let mut fresh = 0;
    loop {
        if fresh < tape.0.len() {
            fill(&mut tape.0[fresh..]).map_err(Stop::Fill)?;
        }
        match step(&tape.0) {
            Step::Done => return Ok(()),
            Step::Failed => return Err(Stop::Failed),
            Step::More { used, requested } => {
                // The contracts bound `used` by the tape's length and make
                // `requested` longer than what is left of it.
                let rest = &tape.0[used..];
                assert!(rest.len() < requested);
                let mut next = Tape(vec![0; requested]);
                next.0[..rest.len()].copy_from_slice(rest);
                fresh = rest.len();
                tape = next;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Step, Stop, Vec, serve, vec};

    /// Each tape keeps the unconsumed suffix in order, and only the bytes
    /// after it are filled.
    #[test]
    fn suffix_is_kept() {
        let mut next = 0u8;
        let mut fills = Vec::new();
        let mut tapes = Vec::new();
        let r: Result<(), Stop<()>> = serve(
            4,
            |buf| {
                fills.push(buf.len());
                for b in buf {
                    *b = next;
                    next += 1;
                }
                Ok(())
            },
            |tape| {
                tapes.push(tape.to_vec());
                match tapes.len() {
                    1 => Step::More {
                        used: 3,
                        requested: 6,
                    },
                    2 => Step::More {
                        used: 0,
                        requested: 7,
                    },
                    _ => Step::Done,
                }
            },
        );
        assert_eq!(r, Ok(()));
        assert_eq!(fills, [4, 5, 1]);
        assert_eq!(
            tapes,
            [
                vec![0, 1, 2, 3],
                vec![3, 4, 5, 6, 7, 8],
                vec![3, 4, 5, 6, 7, 8, 9]
            ]
        );
    }

    #[test]
    fn failures() {
        let mut fills = 0;
        let mut fill = |_: &mut [u8]| -> Result<(), ()> {
            fills += 1;
            Ok(())
        };
        // An operation that fails with no tape draws nothing.
        assert_eq!(serve(0, &mut fill, |_| Step::Failed), Err(Stop::Failed));
        assert_eq!(serve(2, &mut fill, |_| Step::Failed), Err(Stop::Failed));
        assert_eq!(fills, 1);
        let r = serve(1, |_| Err("no randomness"), |_| Step::Done);
        assert_eq!(r, Err(Stop::Fill("no randomness")));
    }
}
