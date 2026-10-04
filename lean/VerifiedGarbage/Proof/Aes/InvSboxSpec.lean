import VerifiedGarbage.Proof.Aes.SboxSpec

/-!
# The specification's inverse S-box, on all 256 inputs at once

As `SboxSpec.lean` does for the S-box: the specification's computation of
the inverse S-box (the inverse of the affine transformation, then the
multiplicative inverse as `b²⁵⁴`) transcribed on truth tables
(`invSboxT`), and proved right input by input (`row_invSboxT`), so that
the kernel evaluates it on the 256 bytes at once.
-/

namespace VG.Proof.Aes

open VG.Spec.Aes VG.Bitslice

/-- The inverse of the affine transformation (`invAffine`). -/
def invAffT (A : List Nat) : List Nat := (List.range 8).map fun i =>
  A.getD ((i + 2) % 8) 0 ^^^ A.getD ((i + 5) % 8) 0 ^^^ A.getD ((i + 7) % 8) 0 ^^^
    (if (0x05 : Nat).testBit i then ONES else 0)

def invSboxT (A : List Nat) : List Nat := powT (invAffT A) 254

theorem length_invAffT (A : List Nat) : (invAffT A).length = 8 := by simp [invAffT]

theorem row_invAffT (A : List Nat) {c : Nat} (hc : c < 256) :
    row (invAffT A) c = invAffine (row A c) := by
  refine row_ext fun j hj => ?_
  simp only [invAffine, BitVec.getLsbD_ofNat, (testBit_sum_pow _ 8).2, hj, decide_true,
    Bool.true_and]
  simp only [invAffT, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, Nat.testBit_xor]
  simp only [← List.getD_eq_getElem?_getD]
  rw [getLsbD_row _ _ (Nat.mod_lt _ (by omega)), getLsbD_row _ _ (Nat.mod_lt _ (by omega)),
    getLsbD_row _ _ (Nat.mod_lt _ (by omega))]
  congr 1
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | omega |
    (simp only [testBit_ite_ONES, hc, decide_true, Bool.and_true] <;> decide)

theorem row_invSboxT (A : List Nat) {c : Nat} (hc : c < 256) :
    row (invSboxT A) c = invSbox (row A c) := by
  rw [invSboxT, row_powT (length_invAffT A) _ hc, row_invAffT _ hc]
  rfl

end VG.Proof.Aes
