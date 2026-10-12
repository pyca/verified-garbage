module

public import VerifiedGarbage.Spec.Sha3
public import VerifiedGarbage.TCB.Artifact

/-!
# Keccak-f[1600] on four interleaved states, as a function

**Trusted** (as every file in `Spec/`). The contract of
`vg_keccak_f1600_x4`, which applies the permutation Keccak-f[1600]
(`keccakF`, FIPS 202 §3.4) to four states at once, so that code that runs
four SHAKE streams side by side (ML-KEM's samplers and PRFs on x86-64, each
256-bit register holding the same lane of the four states) can call one copy
of it instead of repeating it at every use.

The four states are interleaved in one array of 100 `u64`s (`stateX4At`):
lane `i` (`x + 5y`) of state `k` is the `u64` at index `4 i + k`, which is
how four-lane code loads and stores them 32 bytes at a time. `scratch` is
working space, room for a second copy of the states and a table of the 24
round constants in four lanes each: on return its contents are unspecified,
and may hold intermediate values.

The states are secret; only the pointers, which are public, may affect
timing.
-/

@[expose] public section

namespace VG.Spec.Sha3

/-- State `k` (0 to 3) of the four interleaved at `p`: its lane `i` is the
`u64` at index `4 i + k`. -/
def stateX4At (m : Mem) (p : Addr) (k : Nat) : State :=
  Vector.ofFn fun i => m.readW (p + BitVec.ofNat 64 (8 * (4 * i.val + k))) 64

/-- `vg_keccak_f1600_x4(states: *mut [u64; 100], scratch: *mut [u64; 196])`.
`scratch` is working space. -/
def permuteX4Sig : Sig where
  params := [("states", .array true .u64 100), ("scratch", .array true .u64 196)]

/-- Applies Keccak-f[1600] to each of the four states interleaved at
`states`. The states are secret. -/
def permuteX4Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  permuteX4Sig.contract A (post := fun states _scratch m m' _ =>
    ∀ k < 4, stateX4At m' states k = keccakF (stateX4At m states k))
    (stack := stack)

/-- `vg_keccak_f1600_x4` on every target. -/
def permuteX4Api : Api where
  module := "sha3"
  name := "vg_keccak_f1600_x4"
  sig := permuteX4Sig
  contracts := some fun A stack => permuteX4Contract A stack
  summary := "The permutation Keccak-f[1600] (FIPS 202 §3.4) on four states at once: applies \
    it to each of the four states interleaved in `*states`, lane `x + 5y` of state `k` (0 to \
    3) at index `4(x + 5y) + k`.\n\n\
    Contract: `VG.Spec.Sha3.permuteX4Contract`. Constant time: only the pointers may affect \
    timing, not the states."
  safety := ["The contents of `scratch` on return are unspecified."]

end VG.Spec.Sha3
