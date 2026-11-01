module

public import VerifiedGarbage.Spec.Blake2.Contract

/-!
# BLAKE2b and BLAKE2s: the contracts of their internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

The compression functions (`vg_blake2b_compress`, `vg_blake2s_compress`) are
F of RFC 7693 §3.2 on a run of blocks, which the streaming functions call.
`update_scratch` and `finalize_scratch` are `update` and `finalize` with
their working space passed in `scratch`, for functions that call them with
theirs (Argon2's). `scratch` is working space, sized with room for
vectorized implementations: the streaming functions pass theirs to the
compression function, so theirs have room for its scratch and for what they
keep across its calls.
-/

@[expose] public section

namespace VG.Proof.Blake2

open VG.Spec VG.Spec.Blake2

/-! ## BLAKE2b -/

/-- `vg_blake2b_compress(state: *mut [u64; 8], blocks: *const [u8; 128], n: usize, t: u64, last: u32, scratch: *mut [u64; 64])`.
`t` and `last` are public; `scratch` is working space. -/
def compressBSig : Sig where
  params := [("state", .array true .u64 8), ("blocks", .slice false (.array .u8 128) "n"),
    ("t", .int .u64 true), ("last", .int .u32 true), ("scratch", .array true .u64 64)]

/-- Updates the state at `state` with the `n` 128-byte blocks at `blocks`:
block `i` with the offset counter `t + 128 · i` (as a 128-bit integer), and
with the final block flag if `last ≠ 0`. The state and the blocks are
secret. -/
def compressBContract {M : ISA} (A : Abi M) : Contract M :=
  compressBSig.contract A (post := fun state blocks n t last _scratch m m' _ =>
    stateAt 64 m' state = compressBlocks b (stateAt 64 m state) m blocks n.toNat t.toNat (last != 0))

/-- `vg_blake2b_update_scratch(state: *mut [u8; 192], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 72])`:
`vg_blake2b_update` with its working space passed in `scratch`, for
functions that call it with theirs (Argon2's): room for the compression
function's (`compressBSig`, 512 bytes) and the function's own spills (64
bytes). -/
def updateBScratchSig : Sig where
  params := [("state", .array true .u8 192), ("count", .int .u64 true),
    ("data", .slice false .u8 "len"), ("scratch", .array true .u64 72)]

/-- `updateBPost`, whatever `scratch` is. The state and the data are secret. -/
def updateBScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  updateBScratchSig.contract A
    (post := fun state count data len _scratch => updateBPost A.ptrBits state count data len)
    (stack := stack)

/-- `vg_blake2b_finalize_scratch(state: *mut [u8; 192], count: u64, out: *mut [u8; 64], scratch: *mut [u64; 72])`:
`vg_blake2b_finalize` with its working space passed in `scratch` (as for
`updateBScratchSig`), for functions that call it with theirs (Argon2's). -/
def finalizeBScratchSig : Sig where
  params := [("state", .array true .u8 192), ("count", .int .u64 true),
    ("out", .array true .u8 64), ("scratch", .array true .u64 72)]

/-- `finalizeBPost`, whatever `scratch` is. The state is secret. -/
def finalizeBScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finalizeBScratchSig.contract A
    (post := fun state count out _scratch => finalizeBPost A.ptrBits state count out)
    (stack := stack)

/-! ## BLAKE2s -/

/-- `vg_blake2s_compress(state: *mut [u32; 8], blocks: *const [u8; 64], n: usize, t: u64, last: u32, scratch: *mut [u64; 64])`.
`t` and `last` are public; `scratch` is working space. -/
def compressSSig : Sig where
  params := [("state", .array true .u32 8), ("blocks", .slice false (.array .u8 64) "n"),
    ("t", .int .u64 true), ("last", .int .u32 true), ("scratch", .array true .u64 64)]

/-- Updates the state at `state` with the `n` 64-byte blocks at `blocks`:
block `i` with the offset counter `t + 64 · i` (modulo 2⁶⁴, BLAKE2s's counter
being 64 bits), and with the final block flag if `last ≠ 0`. The state and
the blocks are secret. -/
def compressSContract {M : ISA} (A : Abi M) : Contract M :=
  compressSSig.contract A (post := fun state blocks n t last _scratch m m' _ =>
    stateAt 32 m' state = compressBlocks s (stateAt 32 m state) m blocks n.toNat t.toNat (last != 0))

/-- `vg_blake2s_update_scratch(state: *mut [u8; 96], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 72])`:
`vg_blake2s_update` with its working space passed in `scratch`, for
functions that call it with theirs: room for the compression function's
(`compressSSig`, 512 bytes) and the function's own spills (64 bytes). -/
def updateSScratchSig : Sig where
  params := [("state", .array true .u8 96), ("count", .int .u64 true),
    ("data", .slice false .u8 "len"), ("scratch", .array true .u64 72)]

/-- `updateSPost`, whatever `scratch` is. The state and the data are secret. -/
def updateSScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  updateSScratchSig.contract A
    (post := fun state count data len _scratch => updateSPost A.ptrBits state count data len)
    (stack := stack)

/-- `vg_blake2s_finalize_scratch(state: *mut [u8; 96], count: u64, out: *mut [u8; 32], scratch: *mut [u64; 72])`:
`vg_blake2s_finalize` with its working space passed in `scratch` (as for
`updateSScratchSig`), for functions that call it with theirs. -/
def finalizeSScratchSig : Sig where
  params := [("state", .array true .u8 96), ("count", .int .u64 true),
    ("out", .array true .u8 32), ("scratch", .array true .u64 72)]

/-- `finalizeSPost`, whatever `scratch` is. The state is secret. -/
def finalizeSScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finalizeSScratchSig.contract A
    (post := fun state count out _scratch => finalizeSPost A.ptrBits state count out)
    (stack := stack)

end VG.Proof.Blake2
