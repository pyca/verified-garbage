module
public import VerifiedGarbage.Impl.RsaOaep.X86_64
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Spec.Dsa.Generate

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
public import VerifiedGarbage.Proof.Dsa.Generation.Layout
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Bignum.LazyMath
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.X86_64.Csub
public import VerifiedGarbage.Proof.Bignum.X86_64.Exp
public import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
public import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
public import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
public import VerifiedGarbage.Proof.Bignum.X86_64.Row
public import VerifiedGarbage.Proof.Bignum.X86_64.Valid
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Proof.RsaOaep.Scan
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Exp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.Generation.Layout
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.Scan

/-! # Shared concrete arena geometry for composing parameter-generation phases -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

structure GenerationGeometry where
  B : Addr
  F : Addr
  pLen : Nat
  qLen : Nat
  lengths : Spec.Dsa.generationLengthsValid pLen qLen
  arenaBound : B.toNat + usedBytes pLen ≤ 2 ^ 64
  frameBound : F.toNat + frameBytes ≤ 2 ^ 64
  stackSize : 128 ≤ F.toNat
  frameArena : (⟨F, frameBytes⟩ : Region).Disjoint ⟨B, usedBytes pLen⟩
  stackArena : (below F 128).Disjoint ⟨B, usedBytes pLen⟩

def GenerationGeometry.part (p : GenerationGeometry) (offset len : Nat) : Region := ⟨off p.B offset, len⟩
def GenerationGeometry.hash (p : GenerationGeometry) : Addr := off p.B VG.Impl.Dsa.Generation.Layout.hash

theorem GenerationGeometry.width (p : GenerationGeometry) :
    p.pLen = 128 ∨ p.pLen = 256 ∨ p.pLen = 384 := by
  rcases p.lengths with h | h | h <;> simp [h.1]

theorem GenerationGeometry.qWidth (p : GenerationGeometry) : p.qLen = 20 ∨ p.qLen = 32 := by
  rcases p.lengths with h | h | h <;> simp [h.2]

theorem GenerationGeometry.part_sub (p : GenerationGeometry) {d n : Nat} (h : d + n ≤ usedBytes p.pLen) :
    Region.Sub (p.part d n) ⟨p.B, usedBytes p.pLen⟩ := Offset.sub_base p.B h

theorem GenerationGeometry.part_bound (p : GenerationGeometry) {d n : Nat} (h : d + n ≤ usedBytes p.pLen) :
    (off p.B d).toNat + n ≤ 2 ^ 64 := by
  have hb := p.arenaBound
  have hd : d < 2 ^ 64 := by
    have ht : usedBytes p.pLen < 2 ^ 64 := by rcases p.width with hh | hh | hh <;> rw [hh] <;> decide
    omega
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]
  omega

theorem GenerationGeometry.frame_part (p : GenerationGeometry) {d n : Nat} (h : d + n ≤ usedBytes p.pLen) :
    (⟨p.F, frameBytes⟩ : Region).Disjoint (p.part d n) := p.frameArena.sub_right (p.part_sub h)

theorem GenerationGeometry.stack_part (p : GenerationGeometry) {d n : Nat} (h : d + n ≤ usedBytes p.pLen) :
    (below p.F 128).Disjoint (p.part d n) := p.stackArena.sub_right (p.part_sub h)

theorem GenerationGeometry.parts_disjoint (p : GenerationGeometry) {d n e k : Nat}
    (hd : d + n ≤ usedBytes p.pLen) (he : e + k ≤ usedBytes p.pLen)
    (h : d + n ≤ e ∨ e + k ≤ d) : (p.part d n).Disjoint (p.part e k) := by
  have hb := p.arenaBound
  exact Offset.disjoint p.B h (by omega) (by omega)

theorem GenerationGeometry.frame_below (p : GenerationGeometry) :
    (⟨p.F, frameBytes⟩ : Region).Disjoint (below p.F 128) :=
  Offset.base_disjoint_below p.F (by decide)

theorem GenerationGeometry.frame_headers (p : GenerationGeometry) :
    ∀ k < 37, ∀ j < 32, Mem.Sep (off p.F (8 * k)) 8
      (off (off p.B arithmetic) (8 * j)) 8 := by
  intro k hk j hj
  apply (p.frame_part (d := arithmetic) (n := arithmeticBytes) (by
    rcases p.width with hh | hh | hh <;> rw [hh] <;> decide)).sep
  · exact Offset.contains_base _ (by unfold frameBytes; omega) (by omega)
  · exact Offset.contains_base _ (by unfold arithmeticBytes; omega) (by omega)

theorem GenerationGeometry.frame_outside (p : GenerationGeometry) :
    ∀ k < 37, ∀ i < 8, arithmeticBytes ≤ ofs (off p.B arithmetic) (off (off p.F (8 * k)) i) := by
  intro k hk i hi
  rw [off_off]
  exact out_scr (p.frame_part (d := arithmetic) (n := arithmeticBytes) (by
    rcases p.width with hh | hh | hh <;> rw [hh] <;> decide))
    (Offset.contains_base _ (by unfold frameBytes; omega) (by omega))

end VG.Proof.Dsa.X86_64.Generation
