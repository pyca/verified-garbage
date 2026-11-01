module

public import VerifiedGarbage.Spec.Sha1.Contract

/-!
# SHA-1: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

The compression function updates a hash value with whole blocks.
`update_scratch` and `finalize_scratch` are `vg_sha1_update` and
`vg_sha1_finalize` with their working space passed in `scratch`, for
functions that call them with theirs (HMAC's, PBKDF2's).
-/

@[expose] public section

namespace VG.Proof.Sha1

open VG.Spec VG.Spec.Sha1

/-- `vg_sha1_compress(state: *mut [u32; 5], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 14])`.
`scratch` is working space. -/
def compressSig : Sig where
  params := [("state", .array true .u32 5), ("blocks", .slice false (.array .u8 64) "n"),
    ("scratch", .array true .u64 14)]

/-- Updates the hash value at `state` with the `n` 64-byte blocks at
`blocks`. The hash value and the blocks are secret. -/
def compressContract {M : ISA} (A : Abi M) : Contract M :=
  compressSig.contract A (post := fun state blocks n _scratch m m' _ =>
    stateAt m' state = compressBlocks (stateAt m state) m blocks n.toNat)

/-- `vg_sha1_update_scratch(state: *mut [u8; 84], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 20])`:
`vg_sha1_update` with its working space passed in `scratch`, for functions
that call it with theirs (HMAC's, PBKDF2's). -/
def updateScratchSig : Sig where
  params := [("state", .array true .u8 84), ("count", .int .u64 true),
    ("data", .slice false .u8 "len"), ("scratch", .array true .u64 20)]

/-- `updatePost`, whatever `scratch` is. The state and the data are secret. -/
def updateScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  updateScratchSig.contract A (post := fun state count data len _scratch => updatePost A.ptrBits state count data len)
    (writeArgs := true)
    (stack := stack)

/-- `vg_sha1_finalize_scratch(state: *mut [u8; 84], count: u64, out: *mut [u8; 20], scratch: *mut [u64; 20])`:
`vg_sha1_finalize` with its working space passed in `scratch`, for functions
that call it with theirs (HMAC's, PBKDF2's). -/
def finalizeScratchSig : Sig where
  params := [("state", .array true .u8 84), ("count", .int .u64 true),
    ("out", .array true .u8 20), ("scratch", .array true .u64 20)]

/-- `finalizePost`, whatever `scratch` is. The state is secret. -/
def finalizeScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finalizeScratchSig.contract A (post := fun state count out _scratch => finalizePost A.ptrBits state count out)
    (writeArgs := true)
    (stack := stack)

end VG.Proof.Sha1
