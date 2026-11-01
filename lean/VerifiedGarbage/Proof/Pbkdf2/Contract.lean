module

public import VerifiedGarbage.Spec.Pbkdf2.Generic

/-!
# PBKDF2-HMAC over any streaming hash function: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

With the hash function a parameter (`VG.Spec.Hmac.StreamingHash`),
`vg_pbkdf2_hmac_<hash>_iterate` computes step 3's chain `Uⱼ₊₁ = PRF (P, Uⱼ)`,
exclusive-or'ed into `T` (`VG.Spec.Pbkdf2.iterate`), with the password's HMAC key
given as the two streaming states that `vg_hmac_<hash>_init` sets up
(`VG.Spec.Hmac.initContract`), one after the other in `key`. `U` and `T` are as long
as the digest. `scratch` is the number of 64-bit words of working space.

`vg_pbkdf2_hmac_<hash>_scratch` is `vg_pbkdf2_hmac_<hash>` with its working space
passed in `scratch`, for functions that call it with theirs (scrypt's).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2

open VG.Spec VG.Spec.Pbkdf2
open Sha256 (bytesAt)
open Hmac (StreamingHash xorPad ipad opad hmacBlockKey hmac Instance)

variable (S : StreamingHash) (scratch : Nat)

/-- `vg_pbkdf2_hmac_<hash>_iterate(key: *const [u8; 2S], u: *const [u8; D], n: u32, t: *mut [u8; D], scratch: *mut [u64; W])`,
with `S` the size of the streaming state and `D` that of the digest. `n` is
public; `scratch` is working space. -/
def iterateSig : Sig where
  params := [("key", .array false .u8 (2 * S.stateBytes)), ("u", .array false .u8 S.digestBytes),
    ("n", .int .u32 true), ("t", .array true .u8 S.digestBytes), ("scratch", .array true .u64 scratch)]

/-- If, for a key `K₀` of the block size of `H`, the streaming state at `key`
represents `K₀ ⊕ ipad` and the one right after it represents `K₀ ⊕ opad`:
from the digest-sized `U` at `u` and `T` at `t`, runs `n` steps
`U ← HMAC (K₀, U)`, `T ← T ⊕ U`, leaving the final `T` at `t`. The key, `U`
and `T` are secret. -/
def iterateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (iterateSig S scratch).contract A (post := fun key u n t _scratch m m' _ =>
    ∀ k0, k0.length = S.H.blockSize → S.Repr m key (xorPad k0 ipad) →
      S.Repr m (key + BitVec.ofNat 64 S.stateBytes) (xorPad k0 opad) →
      bytesAt m' t S.digestBytes =
        iterate (hmacBlockKey S.H k0) n.toNat (bytesAt m u S.digestBytes) (bytesAt m t S.digestBytes))
    (writeArgs := true)
    (stack := stack)

/-- `vg_pbkdf2_hmac_<hash>_scratch(password: *const u8, password_len: usize, salt: *const u8, salt_len: usize, c: u32, out: *mut u8, out_len: usize, scratch: *mut [u64; W])`:
`vg_pbkdf2_hmac_<hash>` with its working space passed in `scratch`, for
functions that call it with theirs (scrypt's). -/
def pbkdf2ScratchSig : Sig where
  params := [("password", .slice false .u8 "password_len"), ("salt", .slice false .u8 "salt_len"),
    ("c", .int .u32 true), ("out", .slice true .u8 "out_len"), ("scratch", .array true .u64 scratch)]

/-- `pbkdf2Contract`, whatever `scratch` is. -/
def pbkdf2ScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (pbkdf2ScratchSig scratch).contract A
    (pre := fun password passwordLen salt saltLen c out outLen _scratch =>
      pbkdf2Pre S A.ptrBits password passwordLen salt saltLen c out outLen)
    (post := fun password passwordLen salt saltLen c out outLen _scratch =>
      pbkdf2Post S A.ptrBits password passwordLen salt saltLen c out outLen)
    (writeArgs := true)
    (stack := stack)

namespace Instance

variable (I : Instance)

/-- The contract of `vg_pbkdf2_hmac_<hash>_iterate`: `VG.Spec.Pbkdf2.iterateContract`. -/
def iterateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Proof.Pbkdf2.iterateContract I.S I.scratch A stack

/-- The contract of `vg_pbkdf2_hmac_<hash>_scratch`:
`VG.Spec.Pbkdf2.pbkdf2ScratchContract`. -/
def pbkdf2ScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Proof.Pbkdf2.pbkdf2ScratchContract I.S I.pbkdf2Scratch A stack

end Instance

end VG.Proof.Pbkdf2
