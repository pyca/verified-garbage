module

public import VerifiedGarbage.Spec.Sha256.Contract

/-!
# SHA-256: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

The compression function updates a hash value with whole blocks.
`update_scratch` and `finalize_scratch` are `vg_sha256_update` and
`vg_sha256_finalize` with their working space passed in `scratch`, for
functions that call them with theirs (HMAC's, PBKDF2's, ECDSA's, RSA's).
-/

@[expose] public section

namespace VG.Proof.Sha256

open VG.Spec VG.Spec.Sha256

/-- `vg_sha256_compress(state: *mut [u32; 8], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 70])`.
`scratch` is working space, sized for the tightest target: x86-64 with AVX2
keeps the message schedules of two blocks in it (512 bytes), and saves six
callee-saved registers. The other SHA-256 functions, and HMAC-SHA-256's and
PBKDF2-HMAC-SHA-256's, pass theirs to it, so theirs have room for it and for
what they keep across its calls. -/
def compressSig : Sig where
  params := [("state", .array true .u32 8), ("blocks", .slice false (.array .u8 64) "n"),
    ("scratch", .array true .u64 70)]

/-- Updates the hash value at `state` with the `n` 64-byte blocks at
`blocks`. The hash value and the blocks are secret. -/
def compressContract {M : ISA} (A : Abi M) : Contract M :=
  compressSig.contract A (post := fun state blocks n _scratch m m' _ =>
    stateAt m' state = compressBlocks (stateAt m state) m blocks n.toNat)

/-- `vg_sha256_update_scratch(state: *mut [u8; 96], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 76])`:
`vg_sha256_update` with its working space passed in `scratch`, for functions
that call it with theirs (HMAC's, PBKDF2's, ECDSA's). -/
def updateScratchSig : Sig where
  params := [("state", .array true .u8 96), ("count", .int .u64 true),
    ("data", .slice false .u8 "len"), ("scratch", .array true .u64 76)]

/-- `updatePost`, whatever `scratch` is. The state and the data are secret. -/
def updateScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  updateScratchSig.contract A (post := fun state count data len _scratch => updatePost A.ptrBits state count data len)
    (writeArgs := true)
    (stack := stack)

/-- `vg_sha256_finalize_scratch(state: *mut [u8; 96], count: u64, out: *mut [u8; 32], scratch: *mut [u64; 76])`:
`vg_sha256_finalize` with its working space passed in `scratch`, for
functions that call it with theirs (HMAC's, PBKDF2's, ECDSA's). -/
def finalizeScratchSig : Sig where
  params := [("state", .array true .u8 96), ("count", .int .u64 true),
    ("out", .array true .u8 32), ("scratch", .array true .u64 76)]

/-- `finalizePost`, whatever `scratch` is. The state is secret. -/
def finalizeScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finalizeScratchSig.contract A (post := fun state count out _scratch => finalizePost A.ptrBits state count out)
    (writeArgs := true)
    (stack := stack)

end VG.Proof.Sha256
