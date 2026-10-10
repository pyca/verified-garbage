module

public import VerifiedGarbage.Spec.Sha3
public import VerifiedGarbage.TCB.Artifact

/-!
# Keccak-f[1600] on two interleaved states, as a function

**Trusted** (as every file in `Spec/`). The contract of
`vg_keccak_f1600_x2`, which applies the permutation Keccak-f[1600]
(`keccakF`, FIPS 202 §3.4) to two states at once, so that code that runs two
SHAKE streams side by side (ML-DSA's samplers on AArch64, each Neon register
holding the same lane of both states) can call one copy of it instead of
repeating it at every use.

The two states are interleaved in one array of 50 `u64`s (`stateX2At`):
lane `i` (`x + 5y`) of the first is the `u64` at index `2 i`, of the second
the one at index `2 i + 1`, which is how two-lane code loads and stores them
16 bytes at a time. `scratch` is working space: on return its contents are
unspecified, and may hold the caller's registers or intermediate values.

The states are secret; only the pointers, which are public, may affect
timing.
-/

@[expose] public section

namespace VG.Spec.Sha3

/-- State `k` (0 or 1) of the two interleaved at `p`: its lane `i` is the
`u64` at index `2 i + k`. -/
def stateX2At (m : Mem) (p : Addr) (k : Nat) : State :=
  Vector.ofFn fun i => m.readW (p + BitVec.ofNat 64 (8 * (2 * i.val + k))) 64

/-- `vg_keccak_f1600_x2(states: *mut [u64; 50], scratch: *mut [u64; 16])`.
`scratch` is working space. -/
def permuteX2Sig : Sig where
  params := [("states", .array true .u64 50), ("scratch", .array true .u64 16)]

/-- Applies Keccak-f[1600] to each of the two states interleaved at `states`.
The states are secret. -/
def permuteX2Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  permuteX2Sig.contract A (post := fun states _scratch m m' _ =>
    stateX2At m' states 0 = keccakF (stateX2At m states 0) ∧
      stateX2At m' states 1 = keccakF (stateX2At m states 1))
    (stack := stack)

/-- `vg_keccak_f1600_x2` on every target. -/
def permuteX2Api : Api where
  module := "sha3"
  name := "vg_keccak_f1600_x2"
  sig := permuteX2Sig
  contracts := some fun A stack => permuteX2Contract A stack
  summary := "The permutation Keccak-f[1600] (FIPS 202 §3.4) on two states at once: applies it \
    to each of the two states interleaved in `*states`, lane `x + 5y` of the first at index \
    `2(x + 5y)` and of the second at index `2(x + 5y) + 1`.\n\n\
    Contract: `VG.Spec.Sha3.permuteX2Contract`. Constant time: only the pointers may affect \
    timing, not the states."
  safety := ["The contents of `scratch` on return are unspecified."]

end VG.Spec.Sha3
