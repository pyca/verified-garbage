module
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
import VerifiedGarbage.Proof.MlKem.Arith

/-!
# ML-KEM's 16-bit inverse NTT on AArch64: lanes

The inverse butterfly `gs x y z t` (`Impl/MlKem/AArch64/Ntt16.lean`) on one
lane: `x ← x + y`, `y ← (y - x) · z mod q` (`gs_lane`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open Impl.MlKem.AArch64.Ntt16

private theorem toInt_add16' {a r : BitVec 16} (h1 : -32768 ≤ a.toInt + r.toInt)
    (h2 : a.toInt + r.toInt < 32768) : (a + r).toInt = a.toInt + r.toInt := by
  rw [BitVec.toInt_add]; simp only [Int.bmod_def]; split <;> omega

private theorem toInt_sub16' {a r : BitVec 16} (h1 : -32768 ≤ a.toInt - r.toInt)
    (h2 : a.toInt - r.toInt < 32768) : (a - r).toInt = a.toInt - r.toInt := by
  rw [BitVec.toInt_sub]; simp only [Int.bmod_def]; split <;> omega

/-- An inverse butterfly on one lane: `a + b`, and `r = d · z - t · q` for
`d = b - a`, `t = sqrdmulh(d, tw z)`. -/
theorem gs_lane {a b : BitVec 16} {X Y : Zq} {z Bx By : Nat} (ha : LRep a X Bx) (hb : LRep b Y By)
    (hz : z < 3329) (hB : Bx + By ≤ 32768) :
    ∃ t, sqdmulhHLane true (b - a) (BitVec.ofNat 16 (tw z)) = some t ∧
      LRep (a + b) (X + Y) (Bx + By) ∧
      LRep ((b - a) * BitVec.ofNat 16 z - t * BitVec.ofNat 16 3329) (ofNat z * (Y - X)) 3329 := by
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  have hd : (b - a).toInt = b.toInt - a.toInt := toInt_sub16' (by omega) (by omega)
  obtain ⟨t, ht, h1, h2, h3⟩ := mm_ok (b - a) (z := z) (by omega) hz
  refine ⟨t, ht, ?_, ?_⟩
  · have hX := val_lt X
    have hY := val_lt Y
    have e1 : (X + Y).val = (X.val + Y.val) % 3329 := val_add' X Y
    refine ⟨?_, ?_, ?_⟩ <;> rw [toInt_add16' (by omega) (by omega)] <;> [omega; omega; skip]
    rw [e1]; omega
  · refine ⟨h1, h2, ?_⟩
    rw [hd] at h3
    generalize (b - a) * BitVec.ofNat 16 z - t * BitVec.ofNat 16 3329 = r at h1 h2 h3 ⊢
    obtain ⟨k1, hk1⟩ := Int.dvd_of_emod_eq_zero b3
    obtain ⟨k2, hk2⟩ := Int.dvd_of_emod_eq_zero a3
    have hX := val_lt X
    have hY := val_lt Y
    -- `(Y - X).val = Y - X + q·c`
    have eD : ((Y - X).val : Int) = (Y.val : Int) - X.val + 3329 * (if X.val ≤ Y.val then 0 else 1) := by
      rw [val_sub_eq]
      have hq : q = 3329 := rfl
      by_cases h : X.val ≤ Y.val <;> simp only [h, ite_true, ite_false] <;> omega
    have e2 : (ofNat z * (Y - X)).val = z * (Y - X).val % 3329 := by
      rw [val_mul, val_ofNat, Nat.mod_eq_of_lt (show z < q from hz)]
    rw [e2]
    have hm : (b.toInt - a.toInt) * z =
        (((Y - X).val : Int) * z) + 3329 * ((k1 - k2 - (if X.val ≤ Y.val then 0 else 1)) * z) := by
      rw [eD, show b.toInt = Y.val + 3329 * k1 by omega, show a.toInt = X.val + 3329 * k2 by omega]
      split <;> grind
    have hW : ((z * (Y - X).val : Nat) : Int) = ((Y - X).val : Int) * z := by
      rw [Int.natCast_mul, Int.mul_comm]
    rw [hm] at h3
    generalize z * (Y - X).val = W at hW ⊢
    generalize ((Y - X).val : Int) * z = Wi at hW h3
    generalize (k1 - k2 - (if X.val ≤ Y.val then 0 else 1)) * (z : Int) = K at h3
    omega

end VG.Proof.MlKem.AArch64.Ntt16
