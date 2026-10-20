module
public import VerifiedGarbage.Impl.RsaOaep.AArch64
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Spec.Dsa.Generate

import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Impl.Dsa.Layout
import VerifiedGarbage.Proof.Bignum.AArch64.SquareMath
import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.Offset

/-! # Shared concrete arena geometry for composing parameter-generation phases -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

structure GenerationGeometry where
  B : Addr
  F : Addr
  pLen : Nat
  qLen : Nat
  lengths : Spec.Dsa.generationLengthsValid pLen qLen
  arenaBound : B.toNat + usedBytes pLen ≤ 2 ^ 64
  frameBound : F.toNat + frameBytes ≤ 2 ^ 64
  stackSize : 16 ≤ F.toNat
  frameArena : (⟨F, frameBytes⟩ : Region).Disjoint ⟨B, usedBytes pLen⟩
  stackArena : (below F 16).Disjoint ⟨B, usedBytes pLen⟩

def GenerationGeometry.part (p : GenerationGeometry) (offset len : Nat) : Region := ⟨VG.Proof.Bignum.off p.B offset, len⟩
def GenerationGeometry.hash (p : GenerationGeometry) : Addr := VG.Proof.Bignum.off p.B VG.Impl.Dsa.Generation.Layout.hash

theorem GenerationGeometry.width (p : GenerationGeometry) :
    p.pLen = 128 ∨ p.pLen = 256 ∨ p.pLen = 384 := by
  rcases p.lengths with h | h | h <;> simp [h.1]

theorem GenerationGeometry.qWidth (p : GenerationGeometry) : p.qLen = 20 ∨ p.qLen = 32 := by
  rcases p.lengths with h | h | h <;> simp [h.2]

theorem GenerationGeometry.part_sub (p : GenerationGeometry) {d n : Nat} (h : d + n ≤ usedBytes p.pLen) :
    Region.Sub (p.part d n) ⟨p.B, usedBytes p.pLen⟩ := Offset.sub_base p.B h

theorem GenerationGeometry.part_bound (p : GenerationGeometry) {d n : Nat} (h : d + n ≤ usedBytes p.pLen) :
    (VG.Proof.Bignum.off p.B d).toNat + n ≤ 2 ^ 64 := by
  have hb := p.arenaBound
  have hd : d < 2 ^ 64 := by
    have ht : usedBytes p.pLen < 2 ^ 64 := by rcases p.width with hh | hh | hh <;> rw [hh] <;> decide
    omega
  simp only [VG.Proof.Bignum.off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]
  omega

theorem GenerationGeometry.frame_part (p : GenerationGeometry) {d n : Nat} (h : d + n ≤ usedBytes p.pLen) :
    (⟨p.F, frameBytes⟩ : Region).Disjoint (p.part d n) := p.frameArena.sub_right (p.part_sub h)

theorem GenerationGeometry.stack_part (p : GenerationGeometry) {d n : Nat} (h : d + n ≤ usedBytes p.pLen) :
    (below p.F 16).Disjoint (p.part d n) := p.stackArena.sub_right (p.part_sub h)

theorem GenerationGeometry.parts_disjoint (p : GenerationGeometry) {d n e k : Nat}
    (hd : d + n ≤ usedBytes p.pLen) (he : e + k ≤ usedBytes p.pLen)
    (h : d + n ≤ e ∨ e + k ≤ d) : (p.part d n).Disjoint (p.part e k) := by
  have hb := p.arenaBound
  exact Offset.disjoint p.B h (by omega) (by omega)

theorem GenerationGeometry.frame_below (p : GenerationGeometry) :
    (⟨p.F, frameBytes⟩ : Region).Disjoint (below p.F 16) :=
  Offset.base_disjoint_below p.F (by decide)

theorem GenerationGeometry.frame_headers (p : GenerationGeometry) :
    ∀ k < 34, ∀ j < 32, Mem.Sep (VG.Proof.Bignum.off p.F (8 * k)) 8
      (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.B arithmetic) (8 * j)) 8 := by
  intro k hk j hj
  apply (p.frame_part (d := arithmetic) (n := arithmeticBytes) (by
    rcases p.width with hh | hh | hh <;> rw [hh] <;> decide)).sep
  · exact Offset.contains_base _ (by unfold frameBytes; omega) (by omega)
  · exact Offset.contains_base _ (by unfold arithmeticBytes; omega) (by omega)

theorem GenerationGeometry.frame_outside (p : GenerationGeometry) :
    ∀ k < 34, ∀ i < 8, arithmeticBytes ≤ ofs (VG.Proof.Bignum.off p.B arithmetic) (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.F (8 * k)) i) := by
  intro k hk i hi
  rw [VG.Proof.Bignum.off_off]
  exact out_scr (p.frame_part (d := arithmetic) (n := arithmeticBytes) (by
    rcases p.width with hh | hh | hh <;> rw [hh] <;> decide))
    (Offset.contains_base _ (by unfold frameBytes; omega) (by omega))

end VG.Proof.Dsa.AArch64.Generation
