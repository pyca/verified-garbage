module

public import VerifiedGarbage.Spec.Sha3.X2

/-!
# Keccak-f[1600] on three states, as a function

**Trusted** (as every file in `Spec/`). The contract of
`vg_keccak_f1600_x3`, which applies the permutation Keccak-f[1600]
(`keccakF`, FIPS 202 §3.4) to three states at once: two interleaved in one
array, as for `vg_keccak_f1600_x2` (`stateX2At`), and a third in an array of
its own (`stateAt`). An implementation can run the two interleaved states in
vector registers and the third in general registers, side by side, so that a
caller with an unrelated sponge to advance (ML-KEM's encapsulation hashes
its encapsulation key while it samples the matrix with paired SHAKE128) pays
little for it.

`scratch` is working space: on return its contents are unspecified, and may
hold the caller's registers or intermediate values. The function may also
use `stack` bytes of the stack (the contract's `stack`).

The states are secret; only the pointers, which are public, may affect
timing.
-/

@[expose] public section

namespace VG.Spec.Sha3

/-- `vg_keccak_f1600_x3(states: *mut [u64; 50], state: *mut [u64; 25],
scratch: *mut [u64; 16])`. `scratch` is working space. -/
def permuteX3Sig : Sig where
  params := [("states", .array true .u64 50), ("state", .array true .u64 25),
    ("scratch", .array true .u64 16)]

/-- Applies Keccak-f[1600] to each of the two states interleaved at `states`
and to the state at `state`. The states are secret. -/
def permuteX3Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  permuteX3Sig.contract A (post := fun states state _scratch m m' _ =>
    stateX2At m' states 0 = keccakF (stateX2At m states 0) ∧
      stateX2At m' states 1 = keccakF (stateX2At m states 1) ∧
      stateAt m' state = keccakF (stateAt m state))
    (stack := stack)

/-- `vg_keccak_f1600_x3` on every target. -/
def permuteX3Api : Api where
  module := "sha3"
  name := "vg_keccak_f1600_x3"
  sig := permuteX3Sig
  contracts := some fun A stack => permuteX3Contract A stack
  summary := "The permutation Keccak-f[1600] (FIPS 202 §3.4) on three states at once: applies \
    it to each of the two states interleaved in `*states`, lane `x + 5y` of the first at index \
    `2(x + 5y)` and of the second at index `2(x + 5y) + 1`, and to the state `*state`, lane \
    `x + 5y` at index `x + 5y`.\n\n\
    Contract: `VG.Spec.Sha3.permuteX3Contract`. Constant time: only the pointers may affect \
    timing, not the states."
  safety := ["The contents of `scratch` on return are unspecified."]

end VG.Spec.Sha3
