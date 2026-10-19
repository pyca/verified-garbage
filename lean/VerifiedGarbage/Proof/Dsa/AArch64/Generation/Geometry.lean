module
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.RsaOaep.AArch64
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Spec.Dsa.Generate

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcMath
import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
public import VerifiedGarbage.Proof.Dsa.Generation.Layout
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
public import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
public import VerifiedGarbage.Proof.Bignum.AArch64.Copy
public import VerifiedGarbage.Proof.Bignum.AArch64.Csub
public import VerifiedGarbage.Proof.Bignum.AArch64.Double
public import VerifiedGarbage.Proof.Bignum.AArch64.Mont
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
public import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
public import VerifiedGarbage.Proof.Bignum.AArch64.R2dFast
public import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
public import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
public import VerifiedGarbage.Proof.Bignum.AArch64.R2dStep
public import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
public import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
public import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
public import VerifiedGarbage.Proof.Bignum.AArch64.Row
public import VerifiedGarbage.Proof.Bignum.AArch64.Setup
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
public import VerifiedGarbage.Proof.Bignum.AArch64.Store
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Proof.Poly1305.Limbs64
public import VerifiedGarbage.Proof.RsaOaep.Mask
public import VerifiedGarbage.Spec.RsaOaep
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
import VerifiedGarbage.Proof.Bignum.AArch64.R2dFast
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dStep
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.Layout
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.RsaOaep.Mask
import VerifiedGarbage.Spec.RsaOaep

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
