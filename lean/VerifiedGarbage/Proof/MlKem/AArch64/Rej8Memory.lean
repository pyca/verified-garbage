module

public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Batch
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Scalar
public import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16

/-! # Polynomial-prefix effects of the vector rejection stores -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem

theorem coeffAddr_add (p : Addr) (j k : Nat) :
    coeffAddr p j + BitVec.ofNat 64 (4*k) = coeffAddr p (j+k) := by
  simp only [coeffAddr,ptr_add,Nat.mul_add]

/-- A vector store changes exactly four consecutive polynomial words. -/
theorem coeffAt_write16 (m : Mem) (p : Addr) (x : BitVec 128) {i j : Nat}
    (hi : i<256) (hj : j+4≤256) :
    coeffAt (m.write (coeffAddr p j) 16 x) p i =
      if j≤i ∧ i<j+4 then vword x (i-j) else coeffAt m p i := by
  rw [← ofVWords_vword x,write16]
  have h4 : coeffAddr p j+BitVec.ofNat 64 4=coeffAddr p (j+1) := coeffAddr_add p j 1
  have h8 : coeffAddr p j+BitVec.ofNat 64 8=coeffAddr p (j+2) := coeffAddr_add p j 2
  have h12 : coeffAddr p j+BitVec.ofNat 64 12=coeffAddr p (j+3) := coeffAddr_add p j 3
  rw [h4,h8,h12,
    coeffAt_writeW _ p (show i<n from hi) (show j+3<n by change j+3<256; omega),
    coeffAt_writeW _ p (show i<n from hi) (show j+2<n by change j+2<256; omega),
    coeffAt_writeW _ p (show i<n from hi) (show j+1<n by change j+1<256; omega),
    coeffAt_writeW _ p (show i<n from hi) (show j<n by change j<256; omega)]
  rw [ofVWords_vword]
  by_cases h3 : j+3=i
  · rw [ite_eq_left h3,ite_eq_left (by omega),show i-j=3 by omega]
  · rw [ite_eq_right h3]
    by_cases h2 : j+2=i
    · rw [ite_eq_left h2,ite_eq_left (by omega),show i-j=2 by omega]
    · rw [ite_eq_right h2]
      by_cases h1 : j+1=i
      · rw [ite_eq_left h1,ite_eq_left (by omega),show i-j=1 by omega]
      · rw [ite_eq_right h1]
        by_cases h0 : j=i
        · rw [ite_eq_left h0,ite_eq_left (by omega),show i-j=0 by omega]
        · rw [ite_eq_right h0,ite_eq_right (by omega)]

/-- The two stores affect exactly the eight-word reservation, even when
only some of those slots contain accepted coefficients. -/
theorem coeffAt_updatedMem (s : State) {p : Addr} {j i : Nat}
    (h3 : s.gpr .x3=coeffAddr p j) (hj : j+8≤256) (hi : i<256) :
    coeffAt (updatedMem s) p i =
      if j≤i ∧ i<j+4 then vword (wideLo (compactValue (candidatesAt s) (maskAt s)) (s.v .v21)) (i-j)
      else if j+4≤i ∧ i<j+8 then vword (wideHi (compactValue (candidatesAt s) (maskAt s)) (s.v .v21)) (i-(j+4))
      else coeffAt s.mem p i := by
  rw [updatedMem,ite_eq_right Bool.false_ne_true,h3,show coeffAddr p j+16=coeffAddr p (j+4) from coeffAddr_add p j 4,
    coeffAt_write16 _ _ _ hi (by omega),coeffAt_write16 _ _ _ hi (by omega)]
  have h : j+4+4=j+8 := by omega
  rw [h]
  by_cases hlo : j≤i ∧ i<j+4
  · rw [ite_eq_right (by omega),ite_eq_left hlo,ite_eq_left hlo]
  · rw [ite_eq_right hlo]
    by_cases hhi : j+4≤i ∧ i<j+8
    · simp only [ite_eq_left hhi,ite_eq_right hlo]
    · simp only [ite_eq_right hhi,ite_eq_right hlo]

/-- Coefficient `i` after the stores of a batch at coefficient `j`, with either width: the
accepted candidates in order from `j`, zeros after them up to `j + 8`, and the coefficients
before. -/
theorem coeffAtW_updatedMem (w16 : Bool) (s : State) {p : Addr} {j i : Nat}
    (h3 : s.gpr .x3 = cAddr w16 p j) (hj : j+8≤256) (hi : i<256) (hz : ∀ i<8, vhalf (s.v .v21) i=0) :
    (coeffAtW (cw w16) (updatedMem s w16) p i).toNat =
      if j≤i ∧ i<j+8 then
        (if i-j < acceptedCount s then
          (vhalf (candidatesAt s) ((Impl.MlKem.AArch64.Rej8.acceptedLanes (maskAt s)).getD (i-j) 0)).toNat
        else 0)
      else (coeffAtW (cw w16) s.mem p i).toNat := by
  have hm : maskAt s<256 := acceptanceMask_bound (candidatesAt s)
  cases w16
  · show (coeffAt (updatedMem s) p i).toNat = _
    rw [coeffAt_updatedMem s h3 hj hi]
    by_cases hlo : j≤i ∧ i<j+4
    · rw [ite_eq_left hlo, ite_eq_left ⟨hlo.1, by omega⟩,
        (widened_coeffs (candidatesAt s) (s.v .v21) hm hz (i := i-j) (by omega)).1]
      simp only [acceptedCount]
      by_cases c : i-j < (Impl.MlKem.AArch64.Rej8.acceptedLanes (maskAt s)).length <;> simp [c]
    · rw [ite_eq_right hlo]
      by_cases hhi : j+4≤i ∧ i<j+8
      · rw [ite_eq_left hhi, ite_eq_left ⟨by omega, hhi.2⟩,
          (widened_coeffs (candidatesAt s) (s.v .v21) hm hz (i := i-(j+4)) (by omega)).2,
          show 4+(i-(j+4)) = i-j by omega]
        simp only [acceptedCount]
        by_cases c : i-j < (Impl.MlKem.AArch64.Rej8.acceptedLanes (maskAt s)).length <;> simp [c]
      · rw [ite_eq_right hhi, ite_eq_right (by omega)]
        rfl
  · show (coeffAtW 16 (updatedMem s true) p i).toNat = _
    rw [show updatedMem s true = s.mem.write (s.gpr .x3) 16 (compactValue (candidatesAt s) (maskAt s)) from rfl,
      h3, show cAddr true p j = p + BitVec.ofNat 64 (2*j) from rfl, coeffAtW16_write _ _ hj hi]
    by_cases c : j≤i ∧ i<j+8
    · rw [ite_eq_left c, ite_eq_left c, compact_half _ hm (by omega)]
      simp only [acceptedCount]
      by_cases c' : i-j < (Impl.MlKem.AArch64.Rej8.acceptedLanes (maskAt s)).length <;> simp [c']
    · rw [ite_eq_right c, ite_eq_right c]
      rfl

end VG.Proof.MlKem.AArch64.Rej8
