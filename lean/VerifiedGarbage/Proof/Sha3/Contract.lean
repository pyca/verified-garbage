module

public import VerifiedGarbage.Spec.Sha3.Contract
public import VerifiedGarbage.TCB.Artifact

/-!
# SHA-3 and SHAKE: the contracts of their internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

The streaming sponge, `vg_keccak_absorb_scratch`, `vg_keccak_pad` and
`vg_keccak_squeeze` (on the representation `Repr`), in terms of
`Spec/Sha3.lean`, for any target: `A` is the target's calling convention,
and `stack` the number of bytes of stack below the stack pointer that an
implementation's calls and frames use (`Sig.contract`). A hash is computed
from the all-zero state (which represents the empty message) by
`vg_keccak_absorb_scratch` on each piece of the message, `vg_keccak_pad`,
and `vg_keccak_squeeze` from position 0: by the definitions, the output is
then `sponge rate suffix msg outlen`. Further calls of `vg_keccak_squeeze`,
each from the state and position the previous one left, output the bytes
that follow. They may overwrite their arguments passed in memory, where the
calling convention allows it (`writeArgs`). `scratch` is working space,
sized for the target with the fewest registers.

The permutation Keccak-f[1600] (`vg_keccak_f1600`), which the sponge
functions and the functions that run a sponge of their own call; and
`vg_keccak_pad_scratch` and `vg_keccak_squeeze_scratch`, `vg_keccak_pad`
and `vg_keccak_squeeze` with their working space passed in `scratch`, for
functions that call them with their own (the instances', ML-KEM's, ML-DSA's,
Ed448's), as `vg_keccak_absorb_scratch` is `vg_keccak_absorb`'s. The state
is secret; the rate, the position within the block and the
domain-separation suffix are public.
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

end VG.Proof.Sha3
