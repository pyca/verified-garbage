import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CanonicalizeGroup
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon (coeffAt_write16 vword_read16)

theorem canonicalizeGroup_coeff (m : Mem) (p : Addr) {start k : Nat}
    (hs : start+4≤256) (hk : k<256) :
    coeffAt (canonicalizeGroupMem m (coeffAddr p start)) p k =
      if start≤k ∧ k<start+4 then Inverse.signCorrected (coeffAt m p k) else coeffAt m p k := by
  unfold canonicalizeGroupMem
  rw [coeffAt_write16 _ _ hs _ hk]
  split
  · rename_i h
    rw [canonicalizeVector,laneVector_word _ (by omega),VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ (by omega),coeffAddr_add]
    rw [show start+(k-start)=k by omega]
    rfl
  · rfl

/-- Each group leaves every other coefficient unchanged, allowing in-place
iteration without changing the inputs of future groups. -/
theorem canonicalizeGroup_outside (m : Mem) (p : Addr) {start k : Nat}
    (hs : start+4≤256) (hk : k<256) (ho : k<start ∨ start+4≤k) :
    coeffAt (canonicalizeGroupMem m (coeffAddr p start)) p k=coeffAt m p k := by
  rw [canonicalizeGroup_coeff m p hs hk,ite_eq_right (by omega)]

/-- Invariant for the in-place conversion: the processed prefix is corrected,
and all subsequent coefficients still contain the original signed words. -/
def CanonicalizePrefix (initial current : Mem) (p : Addr) (done : Nat) : Prop :=
  ∀ k<256, coeffAt current p k =
    if k<done then Inverse.signCorrected (coeffAt initial p k) else coeffAt initial p k

theorem canonicalizePrefix_zero (m : Mem) (p : Addr) : CanonicalizePrefix m m p 0 := by
  intro k hk
  simp

theorem canonicalizePrefix_step {initial current : Mem} {p : Addr} {done : Nat}
    (hd : done+4≤256) (h : CanonicalizePrefix initial current p done) :
    CanonicalizePrefix initial (canonicalizeGroupMem current (coeffAddr p done)) p (done+4) := by
  intro k hk
  rw [canonicalizeGroup_coeff current p hd hk]
  by_cases before : k<done
  · rw [ite_eq_right (by omega),h k hk,ite_eq_left before,ite_eq_left (by omega)]
  · by_cases inside : k<done+4
    · rw [ite_eq_left (by omega),h k hk,ite_eq_right before,ite_eq_left inside]
    · rw [ite_eq_right (by omega),h k hk,ite_eq_right before,ite_eq_right inside]

theorem canonicalizePrefix_complete {initial current : Mem} {p : Addr}
    (h : CanonicalizePrefix initial current p 256) {k : Nat} (hk : k<256) :
    coeffAt current p k=Inverse.signCorrected (coeffAt initial p k) := by
  rw [h k hk,ite_eq_left hk]

end VG.Proof.MlDsa.AArch64.Optimized.Response
