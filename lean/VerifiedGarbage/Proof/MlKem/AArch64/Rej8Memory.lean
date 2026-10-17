module

public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Batch
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Scalar

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
  rw [updatedMem,h3,show coeffAddr p j+16=coeffAddr p (j+4) from coeffAddr_add p j 4,
    coeffAt_write16 _ _ _ hi (by omega),coeffAt_write16 _ _ _ hi (by omega)]
  have h : j+4+4=j+8 := by omega
  rw [h]
  by_cases hlo : j≤i ∧ i<j+4
  · rw [ite_eq_right (by omega),ite_eq_left hlo,ite_eq_left hlo]
  · rw [ite_eq_right hlo]
    by_cases hhi : j+4≤i ∧ i<j+8
    · simp only [ite_eq_left hhi,ite_eq_right hlo]
    · simp only [ite_eq_right hhi,ite_eq_right hlo]

end VG.Proof.MlKem.AArch64.Rej8
