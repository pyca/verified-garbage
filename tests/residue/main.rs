//! What the library's functions leave on the stack once they return: each
//! operation runs on a thread whose stack is a buffer the test owns
//! (`pthread_attr_setstack`), so that the test can read it afterwards. It
//! runs twice with one secret and twice with another, each time from the
//! same bytes, and the bytes that each pair leaves the same but the two pairs
//! leave different are its residue: what of the secret it left in the dead
//! stack (`zeroize.rs`). Bytes a pair leaves different (e.g. the thread's
//! start-up, or a first call's detection of the CPU features, which a warm-up
//! run does first) are not counted. The operation runs 16 KiB below the
//! thread's start (`below`), so that the thread's exit does not overwrite
//! what it left, and only the bytes below that are counted: the thread's
//! own data and code above it vary between runs.
//!
//! The secret is in a static, which each operation reads through a slice, so
//! that the test's own frames never hold it. The operations of `CLEAN` must
//! leave no residue; the others are measured and reported, until a change
//! makes them clean and adds them there, which holds of optimized builds
//! only (`check`). `control` (no secret) and `leaky`
//! (a copy of the secret in its own frame) check the measurement itself.

#![cfg(all(
    target_os = "linux",
    any(
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "x86"
    )
))]

mod aes_gcm;
mod chacha20poly1305;
mod hmac;
mod sha256;

use std::sync::atomic::{AtomicU8, Ordering};

/// The operations that must leave no residue.
const CLEAN: &[&str] = &["control"];

/// The bytes of the stack each operation runs on.
const STACK: usize = 256 << 10;

static KEY: [AtomicU8; 64] = [const { AtomicU8::new(0) }; 64];

/// The secret of the run: 64 bytes, all `s`-derived.
pub(crate) fn secret() -> &'static [u8] {
    // SAFETY: `AtomicU8` has the size and alignment of `u8`, and no store
    // to `KEY` overlaps a run (`residue` holds `LOCK`).
    unsafe { std::slice::from_raw_parts(KEY.as_ptr().cast::<u8>(), KEY.len()) }
}

static LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

extern "C" fn entry(op: *mut libc::c_void) -> *mut libc::c_void {
    // SAFETY: `run` passes a pointer to a `fn()`, which outlives the thread.
    below(unsafe { *op.cast::<fn()>() });
    std::ptr::null_mut()
}

/// Runs `op` below a frame of `DEPTH` bytes, which it does not write: what
/// the thread runs once `op` has returned (its exit, in the C library) uses
/// the stack above, and leaves `op`'s residue as it is.
#[inline(never)]
fn below(op: fn()) {
    let mut pad = std::mem::MaybeUninit::<[u8; DEPTH]>::uninit();
    // Its address escapes, so the frame keeps it; nothing is called after
    // `op`, which would overwrite what `op` left.
    std::hint::black_box(&mut pad);
    op();
}

/// See `below`.
const DEPTH: usize = 16 << 10;

/// The stack `stack` after running `op` on it, from bytes of 0xA5, with
/// the secret derived from `s`.
fn run(stack: &mut [u8], op: fn(), s: u8) -> Vec<u8> {
    stack.fill(0xA5);
    for (i, k) in KEY.iter().enumerate() {
        k.store(s.wrapping_mul(0x3B) ^ i as u8, Ordering::SeqCst);
    }
    let mut op = op;
    // SAFETY: `attr` and `thread` are initialized by the calls that take them;
    // `stack` is valid for reads and writes of its length, page-aligned
    // (`residue`) and not otherwise used until the thread is joined; `entry`
    // gets a pointer to `op`, which outlives it.
    unsafe {
        let mut attr = std::mem::MaybeUninit::<libc::pthread_attr_t>::uninit();
        assert_eq!(libc::pthread_attr_init(attr.as_mut_ptr()), 0);
        let mut attr = attr.assume_init();
        assert_eq!(
            libc::pthread_attr_setstack(&mut attr, stack.as_mut_ptr().cast(), stack.len()),
            0
        );
        let mut thread = std::mem::MaybeUninit::<libc::pthread_t>::uninit();
        let op = (&raw mut op).cast();
        assert_eq!(
            libc::pthread_create(thread.as_mut_ptr(), &attr, entry, op),
            0
        );
        assert_eq!(
            libc::pthread_join(thread.assume_init(), std::ptr::null_mut()),
            0
        );
        assert_eq!(libc::pthread_attr_destroy(&mut attr), 0);
    }
    // The other thread wrote it: read it afresh.
    (0..stack.len())
        // SAFETY: within `stack`, which the thread, now joined, no longer uses.
        .map(|i| unsafe { std::ptr::read_volatile(stack.as_ptr().add(i)) })
        .collect()
}

/// The bytes of the stack below `DEPTH` that `op` leaves depending on the
/// secret, by their distance below the stack's top.
fn residue(op: fn()) -> Vec<usize> {
    let _guard = LOCK.lock().unwrap();
    let page = 1 << 16;
    let mut buf = vec![0u8; STACK + page];
    let off = buf.as_ptr().align_offset(page);
    let stack = &mut buf[off..off + STACK];
    run(stack, op, 0);
    let (a, a2, b, b2) = (
        run(stack, op, 1),
        run(stack, op, 1),
        run(stack, op, 2),
        run(stack, op, 2),
    );
    (0..STACK)
        .filter(|&i| a[i] == a2[i] && b[i] == b2[i] && a[i] != b[i])
        .map(|i| STACK - i)
        // Only `op` runs below `DEPTH`: the thread's own data (its control
        // block, at the top) and code (its start and exit) are above.
        .filter(|&d| d > DEPTH)
        .collect()
}

/// Measures `op`, which must leave no residue if `name` is in `CLEAN`.
pub(crate) fn check(name: &str, op: fn()) {
    let r = residue(op);
    let n = r.len();
    eprintln!("residue of {name}: {n} bytes");
    // Debug builds keep a copy of what they move, in temporaries of their
    // own: only optimized code is held to `CLEAN` (ci.yml runs these tests
    // with `--release` too).
    let held = CLEAN.contains(&name) && !cfg!(debug_assertions);
    // On a failure, the name and where its bytes are, below the stack's top.
    let left: &[usize] = if held { &r } else { &[] };
    assert_eq!((name, left), (name, &[][..]));
}

/// Uses no secret: leaves no residue on any platform.
#[test]
fn control() {
    check("control", || {
        let mut h = verified_garbage::hashes::sha256::Sha256::new();
        h.update(&[0x5C; 64]);
        std::hint::black_box(h.finalize());
    });
}

/// Keeps a copy of the secret in its own frame: the measurement finds it.
#[test]
fn leaky() {
    #[inline(never)]
    fn copy() {
        let mut x = [0u8; 64];
        x.copy_from_slice(secret());
        std::hint::black_box(&mut x);
    }
    let n = residue(copy).len();
    assert!(n >= 64, "found {n} bytes");
}
