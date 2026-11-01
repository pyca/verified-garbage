module

public import VerifiedGarbage.Spec.ChaCha20
public import VerifiedGarbage.TCB.Artifact

/-!
# ChaCha20: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

* `vg_chacha20_block` writes the block function of a state.
* `vg_chacha20_xor` XORs the keystream of a state into data in place. It
  may overwrite its arguments passed in memory, where the calling
  convention allows it (`writeArgs`), to pass arguments to the functions it
  calls, and takes the number of bytes of stack below the stack pointer
  that an implementation's calls and frames use (`stack`, see
  `Sig.contract`).
* `vg_chacha20_xor_split` is `vg_chacha20_xor` (`xorContract`) on the data
  in `dst` whose first `src_len` bytes are read from `src` instead: the
  first slice of a gathered plaintext encrypted out of place, the rest (a
  TLS record's content type) already copied after it in place, under one
  keystream, with no block of it split between two calls. Its output and
  its input are different buffers (the signature makes the output overlap
  no other buffer, `Sig.contract`), and its input from `src` is at most as
  long as its output.
-/

@[expose] public section

namespace VG.Proof.ChaCha20

open VG.Spec VG.Spec.ChaCha20

/-- `vg_chacha20_block(state: *const [u32; 16], buf: *mut [u32; 64])`. The
first 16 words of `buf` hold the result on exit; the rest is working space. -/
def blockSig : Sig where
  params := [("state", .array false .u32 16), ("buf", .array true .u32 64)]

/-- Writes `block` of the state at `state` to the first 16 words of `buf`.
The state (key, counter and nonce) is secret. -/
def blockContract {M : ISA} (A : Abi M) : Contract M :=
  blockSig.contract A (post := fun state buf m m' _ =>
    stateAt m' buf = block (stateAt m state))

/-- `vg_chacha20_xor(state: *mut [u32; 16], data: *mut u8, len: usize, buf: *mut [u32; 80])`.
`state` is left unspecified, and `buf` is working space: 64 bytes more than
`vg_chacha20_block`'s, so that an implementation that calls it can keep what
it must preserve across the call (e.g. its caller's callee-saved registers)
in `buf` outside the part it passes to the block function. -/
def xorSig : Sig where
  params := [("state", .array true .u32 16), ("data", .slice true .u8 "len"),
    ("buf", .array true .u32 80)]

/-- XORs the first `len` bytes of the keystream of the state at `state` into
the `len` bytes at `data`. The state (key, counter and nonce) and the data
are secret. -/
def xorContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  xorSig.contract A (post := fun state data len _buf m m' _ =>
    bytesAt m' data len.toNat =
      List.zipWith (· ^^^ ·) (bytesAt m data len.toNat) (keystream (stateAt m state) len.toNat))
    (writeArgs := true)
    (stack := stack)

/-- `vg_chacha20_xor_split(state: *mut [u32; 16], src: *const u8, src_len: usize, dst: *mut u8, len: usize, buf: *mut [u32; 80])`.
`state` is left unspecified, and `buf` is working space (as `xorSig`'s). -/
def xorSplitSig : Sig where
  params := [("state", .array true .u32 16), ("src", .slice false .u8 "src_len"),
    ("dst", .slice true .u8 "len"), ("buf", .array true .u32 80)]

/-- The input from `src` is at most as long as the output. -/
def xorSplitPre (pb : Nat) : Curry (xorSplitSig.words pb) (Mem → Prop) :=
  fun _state _src srcLen _dst len _buf _ => srcLen.toNat ≤ len.toNat

/-- For an input from `src` at most as long as the output (`xorSplitPre`):
writes to the `len` bytes at `dst` the `src_len` bytes at `src` followed by
the bytes at `dst` from `src_len` on, XORed with the first `len` bytes of
the keystream of the state at `state` (`xorContract`'s postcondition, with
the data's first `src_len` bytes read from `src`). The state (key, counter
and nonce) and the data are secret. -/
def xorSplitContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  xorSplitSig.contract A (pre := xorSplitPre A.ptrBits)
    (post := fun state src srcLen dst len _buf m m' _ =>
      bytesAt m' dst len.toNat =
        List.zipWith (· ^^^ ·)
          (bytesAt m src srcLen.toNat ++ (bytesAt m dst len.toNat).drop srcLen.toNat)
          (keystream (stateAt m state) len.toNat))
    (writeArgs := true)
    (stack := stack)

end VG.Proof.ChaCha20
