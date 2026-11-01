module

public import VerifiedGarbage.Spec.Sha512.Contract

/-!
# SHA-512: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

The compression function updates a hash value with whole blocks.
`update_scratch` and `finalize_scratch` are `vg_sha512_update` and
`vg_sha512_finalize` with their working space passed in `scratch`, for
functions that call them with theirs (HMAC's, PBKDF2's, Ed25519's).
-/

@[expose] public section

namespace VG.Proof.Sha512

open VG.Spec VG.Spec.Sha512

/-- `vg_sha512_compress(state: *mut [u64; 8], blocks: *const [u8; 128], n: usize, scratch: *mut [u64; 166])`.
`scratch` is working space, sized for the tightest target: x86-64 with AVX2
keeps the message schedules of two blocks in it (1280 bytes), and saves six
callee-saved registers. The other SHA-512 functions, and the HMAC and PBKDF2
functions of the SHA-512 family, pass theirs to it, so theirs have room for
it and for what they keep across its calls. -/
def compressSig : Sig where
  params := [("state", .array true .u64 8), ("blocks", .slice false (.array .u8 128) "n"),
    ("scratch", .array true .u64 166)]

/-- Updates the hash value at `state` with the `n` 128-byte blocks at
`blocks`. The hash value and the blocks are secret. -/
def compressContract {M : ISA} (A : Abi M) : Contract M :=
  compressSig.contract A (post := fun state blocks n _scratch m m' _ =>
    stateAt m' state = compressBlocks (stateAt m state) m blocks n.toNat)

/-- `vg_sha512_update_scratch(state: *mut [u8; 192], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 172])`:
`vg_sha512_update` with its working space passed in `scratch`, for functions
that call it with theirs (HMAC's, PBKDF2's, Ed25519's): 1376 bytes, room for
the compression function's scratch (`compressSig`, 1328 bytes) and the
function's own spills (48 bytes: six saved registers). -/
def updateScratchSig : Sig where
  params := [("state", .array true .u8 192), ("count", .int .u64 true),
    ("data", .slice false .u8 "len"), ("scratch", .array true .u64 172)]

/-- `updatePost`, whatever `scratch` is. The state and the data are secret. -/
def updateScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  updateScratchSig.contract A (post := fun state count data len _scratch => updatePost A.ptrBits state count data len)
    (stack := stack)

/-- `vg_sha512_finalize_scratch(state: *mut [u8; 192], count: u64, out: *mut [u8; 64], scratch: *mut [u64; 172])`:
`vg_sha512_finalize` with its working space passed in `scratch` (1376 bytes,
as for `updateScratchSig`), for functions that call it with theirs (HMAC's,
PBKDF2's, Ed25519's). -/
def finalizeScratchSig : Sig where
  params := [("state", .array true .u8 192), ("count", .int .u64 true),
    ("out", .array true .u8 64), ("scratch", .array true .u64 172)]

/-- `finalizePost`, whatever `scratch` is. The state is secret. -/
def finalizeScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finalizeScratchSig.contract A (post := fun state count out _scratch => finalizePost A.ptrBits state count out)
    (stack := stack)

end VG.Proof.Sha512
