//! Data independent timing (on AArch64, PSTATE.DIT, `FEAT_DIT`): Arm
//! guarantees the timing of the instructions the proofs' leakage model
//! assumes constant time only while it is on.
//!
//! Every operation of this library that may process secrets (MACs, AEADs,
//! ciphers, KDFs, key generation, signing, key agreement, KEMs, RSA's
//! private key and encryption) turns the mode on for the current thread,
//! where the CPU has it, for as long as the call runs, and turns it off
//! again after if it was off. A program making many short calls (an HMAC
//! fed in small pieces, the records of a TLS connection) pays for that in
//! every call: run them in a [`scope`], which turns the mode on once, so
//! that the calls inside find it on and leave it on.
//!
//! On other architectures, and on AArch64 CPUs without `FEAT_DIT`, there is
//! no such mode, and none of this does anything.

// How the library decides (for its developers):
//
// Every verified function takes a `Dit` token first, which only this
// module makes, so the compiler checks that every call of verified code
// comes from an operation that decided whether it needs the mode:
//
// * `enter!` (a `Guard`), for an operation that may process secrets (it
//   takes a key, or produces or hides a secret). It turns data independent
//   timing on for the current thread, where the CPU has it, until the
//   guard is dropped, with the verified function `vg_dit_enter`, and turns
//   it off again with `vg_dit_clear` if it was off before
//   (`lean/VerifiedGarbage/Spec/Dit.lean`, and their effect on it,
//   `VG.Proof.Dit.AArch64.enter_dit` and `clear_dit`). If it was on (in a
//   `scope`), `vg_dit_enter` only reads it. Elsewhere it does nothing: no
//   other target has such a mode.
// * `public`, for an operation whose inputs and outputs are all the
//   caller's public data, for the reason `Why` names: hashing without a
//   key, verifying a signature, checking or converting a public key, and
//   wiping memory. It leaves the mode as it is.
// * `enter_if!`, for a type that is either, as its state says: BLAKE2,
//   keyed or not.
//
// `ci/check_dit.py` checks that each module uses only the reasons its
// algorithms' family allows (`docs/algorithms/`), so a new primitive gets
// the mode its family needs.
//
// An operation enters the mode once and passes its token down: the
// functions it shares with others take the token (`update_with`,
// `digest_with`, …) rather than deciding again. In the tests (debug builds
// with `cfg(test)` or `cpu-features-env`), entering a guard while another
// is live on the thread, or making a token for public work inside an
// operation that holds the mode, panics: the first would turn the mode on
// twice, the second would run part of a secret operation as if it were
// public. So each operation pays for the mode once. A `scope` is the
// caller's, not an operation: the operations inside it decide as usual.

use core::marker::PhantomData;

pub(crate) use verified_garbage_cpu::Dit;

/// Why an operation may run without data independent timing: all of its
/// inputs and outputs are public. `ci/check_dit.py` checks which families
/// may give each.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
// Each target builds only some of the modules that give each reason.
#[allow(dead_code)]
pub(crate) enum Why {
    /// Hashing without a key (SHA-1, SHA-2, SHA-3, SHAKE, BLAKE2 unkeyed,
    /// MD5, SM3): its input is the caller's, and so is the digest. Hashing
    /// a secret calls for a MAC or KDF, which take the mode.
    UnkeyedHash,
    /// Verifying a signature: the public key, message and signature are
    /// public.
    Verify,
    /// Checking, compressing or decompressing a public key.
    PublicKey,
    /// Wiping memory, which stores zeros whatever the data: allowed in
    /// any operation, inside one that holds the mode too.
    Wipe,
    /// A test, which only checks values.
    #[cfg(test)]
    Test,
}

/// Data independent timing on the current thread while it lives (see the
/// module's documentation), and the [`Dit`] tokens that say so
/// ([`Guard::token`]). It is neither `Send` nor `Sync`: the mode is a
/// thread's own.
pub(crate) struct Guard {
    /// Whether this guard holds the mode: made by [`Guard::new`], or by
    /// [`Guard::new_if`] for secret work.
    active: bool,
    /// The mode it holds, if `active`.
    _mode: Mode,
}

/// Data independent timing on the current thread while it lives, where the
/// CPU has it, and back off when dropped if it was off: what a [`Guard`]
/// for secret work and a [`scope`] hold.
struct Mode {
    /// Whether this turned the mode on, which it then turns off when
    /// dropped: it was off, and the CPU has it.
    #[cfg(target_arch = "aarch64")]
    clear: bool,
    _thread: PhantomData<*const ()>,
}

impl Mode {
    /// Turns the mode on, where the CPU has it.
    #[inline]
    fn on() -> Self {
        Mode {
            #[cfg(target_arch = "aarch64")]
            clear: aarch64::enter(),
            _thread: PhantomData,
        }
    }

    /// Leaves the mode as it is.
    #[inline(always)]
    fn kept() -> Self {
        Mode {
            #[cfg(target_arch = "aarch64")]
            clear: false,
            _thread: PhantomData,
        }
    }
}

impl Drop for Mode {
    #[inline]
    fn drop(&mut self) {
        #[cfg(target_arch = "aarch64")]
        if self.clear {
            aarch64::clear();
        }
    }
}

/// Runs `f` with data independent timing on for the current thread (see
/// the [module's documentation](self)), and returns what it returns.
///
/// The library's operations that `f` calls on this thread find the mode on
/// and leave it on, so they only check that it is (on AArch64, one read of
/// PSTATE.DIT each) rather than turning it on and off again. When `f`
/// returns or unwinds, the mode is turned off again if it was off before
/// the scope. Scopes may nest.
///
/// Only the current thread is affected: the library's operations on other
/// threads turn the mode on for themselves, as outside a scope. Everything
/// `f` does runs with the mode on, the caller's own code and the library's
/// public operations (hashing without a key, verifying signatures)
/// included, which on some CPUs makes them slower; so keep the scope around
/// the secret work.
///
/// ```
/// use verified_garbage::dit;
/// use verified_garbage::hashes::sha256::Sha256;
/// use verified_garbage::hmac::Hmac;
///
/// let key = [0x0b; 32];
/// let records: [&[u8]; 3] = [b"one", b"two", b"three"];
/// let mac = dit::scope(|| {
///     let mut h = Hmac::<Sha256>::new(&key);
///     for r in records {
///         h.update(r);
///     }
///     h.finalize()
/// });
/// assert_eq!(mac, Hmac::<Sha256>::mac(&key, b"onetwothree"));
/// ```
#[inline]
pub fn scope<R>(f: impl FnOnce() -> R) -> R {
    let _mode = Mode::on();
    f()
}

impl Guard {
    /// Turns data independent timing on for the current thread, where the
    /// CPU has it.
    #[inline]
    #[track_caller]
    pub(crate) fn new() -> Self {
        check::enter();
        Guard {
            active: true,
            _mode: Mode::on(),
        }
    }

    /// [`Guard::new`] if `secret`, else a guard that leaves the mode as it
    /// is, for public work, as `why` says.
    #[inline]
    #[track_caller]
    pub(crate) fn new_if(secret: bool, why: Why) -> Self {
        if secret {
            Self::new()
        } else {
            let _ = public(why);
            Guard {
                active: false,
                _mode: Mode::kept(),
            }
        }
    }

    /// A token for as long as the guard is borrowed.
    #[inline(always)]
    pub(crate) fn token(&self) -> Dit<'_> {
        // SAFETY: the guard turned the mode on where the CPU has it, and it
        // stays on until the guard is dropped, which the borrow outlives; or
        // its work is public (`new_if`).
        unsafe { Dit::assume() }
    }
}

impl Drop for Guard {
    #[inline]
    fn drop(&mut self) {
        if self.active {
            check::leave();
        }
        // `_mode` turns the mode off after, if it turned it on.
    }
}

#[cfg(target_arch = "aarch64")]
mod aarch64 {
    use super::Dit;
    use crate::arch::dit::{VG_DIT_ENTER_FEATURES, vg_dit_clear, vg_dit_enter};
    use crate::cpu;

    /// Turns PSTATE.DIT on if the CPU has FEAT_DIT (which `VG_CPU_FEATURES`
    /// never removes: see `crate::cpu`), and returns whether it was off then.
    #[inline]
    pub(super) fn enter() -> bool {
        enter_if(cpu::detected().contains(VG_DIT_ENTER_FEATURES))
    }

    /// `enter`, given whether the CPU has FEAT_DIT, so that the tests run
    /// the case without it on any CPU.
    #[inline(always)]
    pub(super) fn enter_if(has: bool) -> bool {
        if !has {
            return false;
        }
        // SAFETY: the CPU has FEAT_DIT, which `vg_dit_enter` requires, and it
        // writes no memory. It is what turns the mode on, and reads no data,
        // so it needs no token but this one.
        unsafe { vg_dit_enter(Dit::assume()) == 0 }
    }

    /// Turns PSTATE.DIT off, after `enter` found it off and turned it on.
    #[inline]
    pub(super) fn clear() {
        // SAFETY: `enter` found FEAT_DIT, which `vg_dit_clear` requires too
        // (`VG_DIT_CLEAR_FEATURES` is the same set), and it writes no memory.
        // It reads no data.
        unsafe { vg_dit_clear(Dit::assume()) }
    }
}

/// The tests' checks that each operation decides once (see the module's
/// documentation): whether a guard is live on this thread.
#[cfg(all(debug_assertions, any(test, feature = "cpu-features-env")))]
mod check {
    extern crate std;

    use core::cell::Cell;

    std::thread_local! {
        static LIVE: Cell<bool> = const { Cell::new(false) };
    }

    #[track_caller]
    pub(super) fn enter() {
        assert!(
            !LIVE.replace(true),
            "a DIT guard entered inside another: pass the operation's token down"
        );
    }

    pub(super) fn leave() {
        LIVE.set(false);
    }

    #[track_caller]
    pub(super) fn public() {
        assert!(
            !LIVE.get(),
            "a public token made inside an operation that holds DIT: pass its token down"
        );
    }
}

/// Without the checks, nothing.
#[cfg(not(all(debug_assertions, any(test, feature = "cpu-features-env"))))]
mod check {
    #[inline(always)]
    pub(super) fn enter() {}
    #[inline(always)]
    pub(super) fn leave() {}
    #[inline(always)]
    pub(super) fn public() {}
}

/// Binds `$dit` to a [`Dit`] token of a new [`Guard`], which keeps data
/// independent timing on until the end of the enclosing block.
macro_rules! enter {
    ($dit:ident) => {
        let guard = $crate::dit::Guard::new();
        let $dit = guard.token();
    };
}
pub(crate) use enter;

/// Binds `$dit` to a token of a [`Guard::new_if`]: data independent timing
/// until the end of the enclosing block if `$secret`, else public work, as
/// the [`Why`] `$why` says.
macro_rules! enter_if {
    ($dit:ident, $secret:expr, $why:expr) => {
        let guard = $crate::dit::Guard::new_if($secret, $why);
        let $dit = guard.token();
    };
}
pub(crate) use enter_if;

/// A token for work whose inputs and outputs are all public, as `why`
/// says: its timing may depend on them, so the mode is left as it is.
#[track_caller]
#[inline(always)]
pub(crate) fn public(why: Why) -> Dit<'static> {
    match why {
        Why::Wipe => {}
        #[cfg(test)]
        Why::Test => {}
        _ => check::public(),
    }
    // SAFETY: `why` says that every input of the verified functions the
    // token is passed to is public, and `check` that no secret operation
    // is running on this thread (in the tests).
    unsafe { Dit::assume() }
}

#[cfg(test)]
mod tests {
    use super::Why;
    #[cfg(target_arch = "aarch64")]
    use crate::arch::dit::{VG_DIT_ENTER_FEATURES, vg_dit_clear, vg_dit_enter};
    #[cfg(target_arch = "aarch64")]
    use crate::cpu;

    /// Whether the CPU has FEAT_DIT.
    #[cfg(target_arch = "aarch64")]
    fn has() -> bool {
        cpu::detected().contains(VG_DIT_ENTER_FEATURES)
    }

    /// Whether PSTATE.DIT is on, read by entering, which leaves it on: this
    /// turns it off again if it was off. Only on a CPU with FEAT_DIT.
    #[cfg(target_arch = "aarch64")]
    fn on() -> bool {
        let dit = super::public(Why::Test);
        // SAFETY: the callers checked for FEAT_DIT, which both functions
        // require; they write no memory.
        unsafe {
            let was = vg_dit_enter(dit) == 1;
            if !was {
                vg_dit_clear(dit);
            }
            was
        }
    }

    /// Entering turns the mode on and reports what it was; clearing turns
    /// it off. This changes PSTATE.DIT of the test's thread alone, and
    /// leaves it off.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn enter_and_clear() {
        assert!(!has() || cycle());
    }

    /// `enter_and_clear` on a CPU with FEAT_DIT; returns true.
    #[cfg(target_arch = "aarch64")]
    fn cycle() -> bool {
        let dit = super::public(Why::Test);
        // SAFETY: the CPU has FEAT_DIT, as both functions require
        // (`VG_DIT_CLEAR_FEATURES` is the same set).
        unsafe {
            vg_dit_enter(dit);
            assert_eq!(vg_dit_enter(dit), 1);
            vg_dit_clear(dit);
            assert_eq!(vg_dit_enter(dit), 0);
            assert_eq!(vg_dit_enter(dit), 1);
            vg_dit_clear(dit);
        }
        true
    }

    /// Without FEAT_DIT, entering does nothing, and leaves nothing to
    /// clear.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn enter_without_dit() {
        assert!(!super::aarch64::enter_if(false));
    }

    /// A guard turns the mode on while it lives, where the CPU has it, and
    /// leaves it off after; one for public work leaves it as it is.
    #[test]
    fn guard() {
        #[cfg(target_arch = "aarch64")]
        let has = has();
        #[cfg(target_arch = "aarch64")]
        if has {
            // SAFETY: the CPU has FEAT_DIT; it writes no memory.
            unsafe { vg_dit_clear(super::public(Why::Test)) };
        }
        {
            super::enter!(dit);
            let _ = dit;
            #[cfg(target_arch = "aarch64")]
            assert!(!has || on());
            // Wiping needs no decision of its own.
            let _ = super::public(Why::Wipe);
        }
        #[cfg(target_arch = "aarch64")]
        assert!(!has || !on());
        {
            super::enter_if!(dit, true, Why::UnkeyedHash);
            let _ = dit;
            #[cfg(target_arch = "aarch64")]
            assert!(!has || on());
        }
        {
            super::enter_if!(dit, false, Why::UnkeyedHash);
            let _ = dit;
            #[cfg(target_arch = "aarch64")]
            assert!(!has || !on());
            // A public guard holds nothing, so a secret operation may follow.
            super::enter!(inner);
            let _ = inner;
        }
        #[cfg(target_arch = "aarch64")]
        assert!(!has || !on());
    }

    /// A scope keeps the mode on while `f` runs, where the CPU has it: a
    /// guard inside finds it on and leaves it on, and so does a scope
    /// inside; public work inside is allowed. After the scope, returning or
    /// unwinding, the mode is off again, as it was.
    #[test]
    fn scope() {
        extern crate std;

        #[cfg(target_arch = "aarch64")]
        let has = has();
        #[cfg(target_arch = "aarch64")]
        if has {
            // SAFETY: the CPU has FEAT_DIT; it writes no memory.
            unsafe { vg_dit_clear(super::public(Why::Test)) };
        }
        let r = super::scope(|| {
            #[cfg(target_arch = "aarch64")]
            assert!(!has || on());
            {
                super::enter!(dit);
                let _ = dit;
            }
            #[cfg(target_arch = "aarch64")]
            assert!(!has || on());
            super::scope(|| {
                let _ = super::public(Why::UnkeyedHash);
            });
            #[cfg(target_arch = "aarch64")]
            assert!(!has || on());
            7
        });
        assert_eq!(r, 7);
        #[cfg(target_arch = "aarch64")]
        assert!(!has || !on());
        let unwound = std::panic::catch_unwind(|| super::scope(|| panic!("inside a scope")));
        assert!(unwound.is_err());
        #[cfg(target_arch = "aarch64")]
        assert!(!has || !on());
    }

    /// Entering a guard inside another panics in the tests.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "a DIT guard entered inside another")]
    fn nested_guard() {
        super::enter!(outer);
        let _ = outer;
        super::enter!(inner);
        let _ = inner;
    }

    /// Making a token for public work inside a secret operation panics in
    /// the tests.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "a public token made inside an operation that holds DIT")]
    fn public_inside_guard() {
        super::enter!(dit);
        let _ = dit;
        let _ = super::public(Why::UnkeyedHash);
    }
}
