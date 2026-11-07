module

public import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Argon2: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

The compression function G (`vg_argon2_compress`, RFC 9106 §3.5–3.6) and
H′ (`vg_argon2_hprime`, §3.3), which the derivation calls.
-/

@[expose] public section

namespace VG.Proof.Argon2

open VG.Spec VG.Spec.Argon2
open Blake2 (bytesAt)

/-- A block at `p`, decoded as little-endian words. -/
def blockAt (m : Mem) (p : Addr) : Block :=
  Vector.ofFn fun j => m.read (p + BitVec.ofNat 64 (8 * j.val)) 8

/-- `vg_argon2_compress(x: *const [u64; 128], y: *const [u64; 128],
out: *mut [u64; 128], scratch: *mut [u64; 512])`.
G: two input blocks, one output block and 4 KiB of working space. -/
def compressSig : Sig where
  params := [("x", .array false .u64 128), ("y", .array false .u64 128),
    ("out", .array true .u64 128), ("scratch", .array true .u64 512)]

/-- Writes G of the blocks at `x` and `y` to `out`. The blocks are secret. -/
def compressContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  compressSig.contract A
    (post := fun x y out _scratch m m' _ => blockAt m' out = compress (blockAt m x) (blockAt m y))
    (writeArgs := true) (stack := stack)

end VG.Proof.Argon2
