module

public import VerifiedGarbage.Spec.Sha3
public import VerifiedGarbage.TCB.Artifact

/-!
# Keccak-f[1600] on two and three states: the contracts of internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

`vg_keccak_f1600_x2` applies the permutation Keccak-f[1600] (`keccakF`,
FIPS 202 §3.4) to two states at once, so that code that runs two SHAKE
streams side by side (ML-DSA's samplers on AArch64, each Neon register
holding the same lane of both states) can call one copy of it instead of
repeating it at every use. The two states are interleaved in one array of
50 `u64`s (`stateX2At`): lane `i` (`x + 5y`) of the first is the `u64` at
index `2 i`, of the second the one at index `2 i + 1`, which is how two-lane
code loads and stores them 16 bytes at a time.

`vg_keccak_f1600_x3` applies it to three states at once: two interleaved in
one array, as for `vg_keccak_f1600_x2`, and a third in an array of its own
(`stateAt`). An implementation can run the two interleaved states in vector
registers and the third in general registers, side by side, so that a
caller with an unrelated sponge to advance (ML-KEM's encapsulation hashes
its encapsulation key while it samples the matrix with paired SHAKE128) pays
little for it.

`scratch` is working space: on return its contents are unspecified, and may
hold the caller's registers or intermediate values. The functions may also
use `stack` bytes of the stack (the contract's `stack`). The states are
secret; only the pointers, which are public, may affect timing.
-/

@[expose] public section

namespace VG.Proof.Sha3

open VG.Spec.Sha3

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

end VG.Proof.Sha3
