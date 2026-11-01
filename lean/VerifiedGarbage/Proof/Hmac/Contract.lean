module

public import VerifiedGarbage.Spec.Hmac.Generic

/-!
# HMAC over any streaming hash function: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

`init_scratch` and `finalize_scratch` are `vg_hmac_<hash>_init` and
`vg_hmac_<hash>_finalize` with their working space passed in `scratch`
(`Instance.scratch` 64-bit words, which hold the working space of the functions
they call), for functions that call them with theirs (PBKDF2's, ECDSA's).
-/

@[expose] public section

namespace VG.Proof.Hmac

open VG.Spec VG.Spec.Hmac
open Sha256 (bytesAt)

variable (S : StreamingHash) (scratch : Nat)

/-- `vg_hmac_<hash>_init_scratch(inner: *mut [u8; S], outer: *mut [u8; S], key: *const u8, key_len: usize, scratch: *mut [u64; W])`:
`init` with its working space passed in `scratch`, for functions that call
it with theirs (PBKDF2's, ECDSA's). -/
def initScratchSig : Sig where
  params := [("inner", .array true .u8 S.stateBytes), ("outer", .array true .u8 S.stateBytes),
    ("key", .slice false .u8 "key_len"), ("scratch", .array true .u64 scratch)]

/-- `initContract`, whatever `scratch` is. -/
def initScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (initScratchSig S scratch).contract A
    (pre := fun inner outer key keyLen _scratch => initPre S A.ptrBits inner outer key keyLen)
    (post := fun inner outer key keyLen _scratch => initPost S A.ptrBits inner outer key keyLen)
    (writeArgs := true)
    (stack := stack)

/-- `vg_hmac_<hash>_finalize_scratch(inner: *mut [u8; S], outer: *const [u8; S], count: u64, out: *mut [u8; D], scratch: *mut [u64; W])`:
`finalize` with its working space passed in `scratch`, for functions that
call it with theirs (PBKDF2's, ECDSA's). -/
def finalizeScratchSig : Sig where
  params := [("inner", .array true .u8 S.stateBytes), ("outer", .array false .u8 S.stateBytes),
    ("count", .int .u64 true), ("out", .array true .u8 S.digestBytes),
    ("scratch", .array true .u64 scratch)]

/-- `finalizeContract`, whatever `scratch` is. -/
def finalizeScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (finalizeScratchSig S scratch).contract A
    (post := fun inner outer count out _scratch => finalizePost S A.ptrBits inner outer count out)
    (writeArgs := true)
    (stack := stack)

namespace Instance

variable (I : Instance)

/-- The contract of `vg_hmac_<hash>_init_scratch`: `VG.Spec.Hmac.initScratchContract`. -/
def initScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Proof.Hmac.initScratchContract I.S I.scratch A stack

/-- The contract of `vg_hmac_<hash>_finalize_scratch`: `VG.Spec.Hmac.finalizeScratchContract`. -/
def finalizeScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Proof.Hmac.finalizeScratchContract I.S I.scratch A stack

end Instance

end VG.Proof.Hmac
