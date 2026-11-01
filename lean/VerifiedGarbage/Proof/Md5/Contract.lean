module

public import VerifiedGarbage.Spec.Md5.Contract

/-!
# MD5: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

The compression function updates a hash value with whole blocks.
`update_scratch` and `finalize_scratch` are `vg_md5_update` and
`vg_md5_finalize` with their working space passed in `scratch`, for
functions that call them with theirs (HMAC's, PBKDF2's).
-/

@[expose] public section

namespace VG.Proof.Md5

open VG.Spec VG.Spec.Md5

/-- `vg_md5_compress(state: *mut [u32; 4], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 8])`.
`scratch` is working space. -/
def compressSig : Sig where
  params := [("state", .array true .u32 4), ("blocks", .slice false (.array .u8 64) "n"),
    ("scratch", .array true .u64 8)]

/-- Updates the MD buffer at `state` with the `n` 64-byte blocks at
`blocks`. The MD buffer and the blocks are secret. -/
def compressContract {M : ISA} (A : Abi M) : Contract M :=
  compressSig.contract A (post := fun state blocks n _scratch m m' _ =>
    stateAt m' state = compressBlocks (stateAt m state) m blocks n.toNat)

/-- `vg_md5_update_scratch(state: *mut [u8; 80], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 14])`:
`vg_md5_update` with its working space passed in `scratch`, for functions
that call it with theirs (HMAC's, PBKDF2's). -/
def updateScratchSig : Sig where
  params := [("state", .array true .u8 80), ("count", .int .u64 true),
    ("data", .slice false .u8 "len"), ("scratch", .array true .u64 14)]

/-- `updatePost`, whatever `scratch` is. The state and the data are secret. -/
def updateScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  updateScratchSig.contract A (post := fun state count data len _scratch => updatePost A.ptrBits state count data len)
    (writeArgs := true)
    (stack := stack)

/-- `vg_md5_finalize_scratch(state: *mut [u8; 80], count: u64, out: *mut [u8; 16], scratch: *mut [u64; 14])`:
`vg_md5_finalize` with its working space passed in `scratch`, for functions
that call it with theirs (HMAC's, PBKDF2's). -/
def finalizeScratchSig : Sig where
  params := [("state", .array true .u8 80), ("count", .int .u64 true),
    ("out", .array true .u8 16), ("scratch", .array true .u64 14)]

/-- `finalizePost`, whatever `scratch` is. The state is secret. -/
def finalizeScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finalizeScratchSig.contract A (post := fun state count out _scratch => finalizePost A.ptrBits state count out)
    (writeArgs := true)
    (stack := stack)

end VG.Proof.Md5
