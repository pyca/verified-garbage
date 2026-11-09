module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseWord
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

theorem umin_word (a b : BitVec 32) :
    (if a.toNat≤b.toNat then a else b) = BitVec.ofNat 32 (min a.toNat b.toNat) := by
  split
  · rw [Nat.min_eq_left (by assumption),BitVec.ofNat_toNat,BitVec.setWidth_eq]
  · rw [Nat.min_eq_right (by omega),BitVec.ofNat_toNat,BitVec.setWidth_eq]

theorem word_and (a b : BitVec 128) (e : Nat) :
    vword (a &&& b) e = vword a e &&& vword b e := by
  simp only [vword,BitVec.extractLsb'_and]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
