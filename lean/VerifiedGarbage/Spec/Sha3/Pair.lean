import VerifiedGarbage.Spec.Sha3.Contract

/-!
# Two Keccak-f[1600] permutations at once: the contract, on every target

**Trusted** (as every file in `Spec/`). The contract of a function that
applies Keccak-f[1600] (`Spec/Sha3.lean`, `keccakF`) to two states at once,
so that code running two sponges side by side (ML-DSA's and ML-KEM's
samplers on AArch64, which keep two states in the two 64-bit halves of
vector registers) can call one copy of the paired permutation instead of
repeating it in every sampler:

* `vg_keccak_f1600x2(states: *mut [u64; 50])`: the two states are packed lane
  by lane, lane `i` (`x + 5y`) of state `j` (0 or 1) at word `2 i + j`
  (`pairStateAt`), as a vector register holds lane `i` of both.

It is the permutation of FIPS 202 §3.4 on each state; nothing else of the
standard. The states are secret, the pointer public, and the function is
constant time.
-/

namespace VG.Spec.Sha3

/-- State `j` of the two packed at `p`: lane `i` is the word at `p + 16 i + 8 j`. -/
def pairStateAt (m : Mem) (p : Addr) (j : Nat) : State :=
  Vector.ofFn fun i => m.readW (p + BitVec.ofNat 64 (16 * i.val + 8 * j)) 64

/-- `vg_keccak_f1600x2(states: *mut [u64; 50])`. -/
def permutePairSig : Sig where
  params := [("states", .array true .u64 50)]

/-- Applies Keccak-f[1600] to each of the two states packed at `states`. -/
def permutePairContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  permutePairSig.contract A (post := fun states m m' _ =>
    pairStateAt m' states 0 = keccakF (pairStateAt m states 0) ∧
      pairStateAt m' states 1 = keccakF (pairStateAt m states 1))
    (stack := stack)

/-- `vg_keccak_f1600x2` on every target. -/
def permutePairApi : Api where
  module := "sha3"
  name := "vg_keccak_f1600x2"
  sig := permutePairSig
  contracts := some fun A stack => permutePairContract A stack
  summary := "Two permutations Keccak-f[1600] (FIPS 202 §3.4) at once: applies it to each of the \
    two states packed lane by lane at `states`, lane `x + 5y` of state `j` (0 or 1) at index \
    `2 (x + 5y) + j`.\n\n\
    Contract: `VG.Spec.Sha3.permutePairContract`. Constant time: only the pointer may affect \
    timing, not the states."
  safety := []

end VG.Spec.Sha3
