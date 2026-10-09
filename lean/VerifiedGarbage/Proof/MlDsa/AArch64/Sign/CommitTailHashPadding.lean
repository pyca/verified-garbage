import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailModel
import VerifiedGarbage.Proof.Sha3.Stream

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.Spec.Sha3
open VG.Proof.Sha3

theorem xorWord_byte (A : Spec.Sha3.State) (j k : Nat) (b : Byte) (w : BitVec 64)
    (hk : k<8) (hw : ∀r<8,w.extractLsb' (8*r) 8=if r=k then b else 0) :
    xorWord A j w=xorByte A (8*j+k) b := by
  apply ext_bytes
  intro i hi
  rw [byteOf_xorByte _ _ _ hi]
  simp only [byteOf,xorWord_get _ _ _ _ (by omega : i/8<25)]
  by_cases he : i/8=j
  · rw [ite_eq_left he,BitVec.extractLsb'_xor,hw _ (by omega)]
    by_cases hr : i%8=k
    · rw [ite_eq_left hr,ite_eq_left (by omega : i=8*j+k)]
    · rw [ite_eq_right hr,ite_eq_right (by omega : i≠8*j+k)]
      exact BitVec.xor_zero
  · rw [ite_eq_right he,ite_eq_right (by omega : i≠8*j+k)]

theorem xorWord_suffix (A : Spec.Sha3.State) (j : Nat) :
    xorWord A j 0x1f=xorByte A (8*j) 0x1f := by
  simpa only [Nat.add_zero] using xorWord_byte A j 0 0x1f 0x1f (by decide) (by
    intro r hr
    rcases (show r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 by omega) with
      rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel)

theorem xorWord_terminal (A : Spec.Sha3.State) :
    xorWord A 16 0x8000000000000000=xorByte A 135 0x80 := by
  exact xorWord_byte A 16 7 0x80 0x8000000000000000 (by decide) (by
    intro r hr
    rcases (show r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 by omega) with
      rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel)

theorem paddedState_bytes (A : Spec.Sha3.State) (j : Nat) :
    paddedState A j=xorByte (xorByte A (8*j) 0x1f) 135 0x80 := by
  rw [paddedState,xorWord_suffix,xorWord_terminal]

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
