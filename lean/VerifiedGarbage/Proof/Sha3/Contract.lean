module

public import VerifiedGarbage.Spec.Sha3.Contract

/-!
# SHA-3 and SHAKE: the contracts of their internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

The permutation Keccak-f[1600] (`vg_keccak_f1600`), which the sponge
functions and the functions that run a sponge of their own call; and
`vg_keccak_pad_scratch` and `vg_keccak_squeeze_scratch`, `vg_keccak_pad`
and `vg_keccak_squeeze` with their working space passed in `scratch`, for
functions that call them with their own (ML-KEM's, ML-DSA's, Ed448's), as
`vg_keccak_absorb_scratch` is `vg_keccak_absorb`'s. The state is secret;
the rate, the position within the block and the domain-separation suffix
are public.
-/

@[expose] public section

namespace VG.Proof.Sha3

open VG.Spec.Sha3

/-- `vg_keccak_f1600(state: *mut [u64; 25], scratch: *mut [u64; 64])`.
`scratch` is working space. -/
def permuteSig : Sig where
  params := [("state", .array true .u64 25), ("scratch", .array true .u64 64)]

/-- Applies Keccak-f[1600] to the state at `state`. The state is secret. -/
def permuteContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  permuteSig.contract A (post := fun state _scratch m m' _ =>
    stateAt m' state = keccakF (stateAt m state))
    (stack := stack)

/-- `vg_keccak_pad_scratch(state: *mut [u64; 25], rate: usize, pos: usize, suffix: u32, scratch: *mut [u64; 80])`:
`vg_keccak_pad` with its working space passed in `scratch`, for functions
that call it with theirs. -/
def padScratchSig : Sig where
  params := [("state", .array true .u64 25), ("rate", .int .usize true),
    ("pos", .int .usize true), ("suffix", .int .u32 true), ("scratch", .array true .u64 80)]

/-- `padPre` and `padPost`, whatever `scratch` is. -/
def padScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  padScratchSig.contract A
    (pre := fun state rate pos suffix _scratch => padPre A.ptrBits state rate pos suffix)
    (post := fun state rate pos suffix _scratch => padPost A.ptrBits state rate pos suffix)
    (writeArgs := true) (stack := stack)

/-- `vg_keccak_squeeze_scratch(state: *mut [u64; 25], rate: usize, pos: usize, out: *mut u8, outlen: usize, scratch: *mut [u64; 80]) -> usize`:
`vg_keccak_squeeze` with its working space passed in `scratch`, for
functions that call it with theirs. -/
def squeezeScratchSig : Sig where
  params := [("state", .array true .u64 25), ("rate", .int .usize true),
    ("pos", .int .usize true), ("out", .slice true .u8 "outlen"),
    ("scratch", .array true .u64 80)]
  ret := some .usize

/-- `squeezePre` and `squeezePost`, whatever `scratch` is. -/
def squeezeScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  squeezeScratchSig.contract A
    (pre := fun state rate pos out outlen _scratch =>
      squeezePre A.ptrBits state rate pos out outlen)
    (post := fun state rate pos out outlen _scratch =>
      squeezePost A.ptrBits state rate pos out outlen)
    (writeArgs := true) (stack := stack)

end VG.Proof.Sha3
