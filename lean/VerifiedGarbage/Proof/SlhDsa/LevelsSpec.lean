module

-- separate module: the specification's facts, which every target's proof of `levels` uses

public import VerifiedGarbage.Proof.SlhDsa.Internal
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA: the heights `levels` computes, one at a time

Target-independent facts about `upNodes` (`Proof/SlhDsa/Internal.lean`):
the nodes of each height from those below (`step`, `upNodes_succ`), and
their number.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.Levels

open VG VG.Spec.SlhDsa VG.Proof.SlhDsa

/-! ## The heights, one at a time -/

section Spec
variable (p : Params) (pkSeed a16 : List Byte) (ty kp base : Nat)

/-- The nodes of height `z + 1` from those `L` of height `z`. -/
def step (z : Nat) (L : List (List Byte)) : List (List Byte) :=
  (List.range (L.length / 2)).map fun j =>
    H p pkSeed (nodeAdrs a16 ty kp (z + 1) (base / 2 ^ (z + 1) + j)) (L.getD (2 * j) [] ++ L.getD (2 * j + 1) [])

theorem upNodes_succ : ∀ (r z : Nat) (L : List (List Byte)),
    upNodes p pkSeed a16 ty kp base z L (r + 1) = step p pkSeed a16 ty kp base (z + r) (upNodes p pkSeed a16 ty kp base z L r)
  | 0, z, L => by simp [upNodes, step]
  | r + 1, z, L => by
    rw [upNodes, upNodes_succ r (z + 1), upNodes, show z + 1 + r = z + (r + 1) by omega_using []]

theorem length_step (z : Nat) (L : List (List Byte)) : (step p pkSeed a16 ty kp base z L).length = L.length / 2 := by
  simp [step]

theorem length_upNodes : ∀ (r z : Nat) (L : List (List Byte)),
    (upNodes p pkSeed a16 ty kp base z L r).length = L.length / 2 ^ r
  | 0, _, _ => by simp [upNodes]
  | r + 1, z, L => by
    rw [upNodes_succ, length_step, length_upNodes r, Nat.pow_succ, Nat.div_div_eq_div_mul]

theorem getD_step (z : Nat) (L : List (List Byte)) {j : Nat} (hj : j < L.length / 2) :
    (step p pkSeed a16 ty kp base z L).getD j [] =
      H p pkSeed (nodeAdrs a16 ty kp (z + 1) (base / 2 ^ (z + 1) + j)) (L.getD (2 * j) [] ++ L.getD (2 * j + 1) []) := by
  simp [step, List.getD_eq_getElem?_getD, hj]

end Spec

end VG.Proof.SlhDsa.X86_64.Levels
