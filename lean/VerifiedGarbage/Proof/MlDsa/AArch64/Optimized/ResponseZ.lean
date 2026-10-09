import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseMath

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa

theorem canonical_signed {a : BitVec 32} (ha : a.toNat<8380417) : a.toInt=(a.toNat:Int) := by
  rw [BitVec.toInt_eq_toNat_cond]
  split <;> omega

theorem addReduced_int (a b : BitVec 32) (ha : a.toNat<8380417)
    (hb : -8380417<b.toInt ∧ b.toInt<2*8380417) :
    (reduceWord (a+b)).toInt=reduce32 ((a.toNat:Int)+b.toInt) := by
  have hat := canonical_signed ha
  have hs : (a+b).toInt=(a.toNat:Int)+b.toInt := by
    rw [addWord_int _ _ (by omega) (by omega),hat]
  rw [reduceWord_int _ (by rw [hs]; omega) (by rw [hs]; omega),hs]

theorem addReduced_norm (a b : BitVec 32) (B : Nat) (ha : a.toNat<8380417)
    (hb : -8380417<b.toInt ∧ b.toInt<2*8380417) (hB : 1≤B) (hB' : B≤524288) :
    (reduceWord (a+b)+BitVec.ofNat 32 (B-1)).toNat<2*B-1 ↔
      normZq (ofInt ((a.toNat:Int)+b.toInt))<B := by
  have hl : -2*8380417<(a.toNat:Int)+b.toInt := by omega
  have hh : (a.toNat:Int)+b.toInt<3*8380417 := by omega
  have hi := addReduced_int a b ha hb
  have hbnd := reduce32_bounds hl hh
  rw [norm_interval _ B hB hB' (by rw [hi]; omega) (by rw [hi]; omega),hi]
  exact (reduce32_norm_iff _ _ hl hh hB').symm

/-- Acceptance makes the stored signed z small enough for the existing
accepted-only canonicalization and signature packing adapter. -/
theorem addReduced_accepted (a b : BitVec 32) (B : Nat) (ha : a.toNat<8380417)
    (hb : -8380417<b.toInt ∧ b.toInt<2*8380417) (hB' : B≤524288)
    (haccept : normZq (ofInt ((a.toNat:Int)+b.toInt))<B) :
    -(B:Int)<(reduceWord (a+b)).toInt ∧ (reduceWord (a+b)).toInt<(B:Int) := by
  have hi := addReduced_int a b ha hb
  rw [hi]
  exact (reduce32_norm_iff _ _ (by omega) (by omega) hB').mp haccept

end VG.Proof.MlDsa.AArch64.Optimized.Response
