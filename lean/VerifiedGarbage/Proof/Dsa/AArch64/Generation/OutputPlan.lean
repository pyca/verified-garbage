module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecOut
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Output

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OutputCopy
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArenaSource
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryWork
import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # The caller's output is disjoint from every parameter-search workspace -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

structure OutputPlan (p : GenerationContext) : Prop where
  lengthSlot : p.saved 7 = BitVec.ofNat 64 (2 * p.geo.pLen + p.geo.qLen)
  bound : (p.saved 6).toNat + (2 * p.geo.pLen + p.geo.qLen) ≤ 2 ^ 64
  separate : ∀ r ∈ p.changed, (⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ : Region).Disjoint r

theorem OutputPlan.apart {p : GenerationContext} (o : OutputPlan p) :
    Apart p.geo.F p.geo.hash ⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ := by
  have hh := p.geo.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  refine ⟨o.separate ⟨p.geo.F, frameBytes⟩ (by simp [GenerationContext.changed]), ?_, ?_⟩
  · exact (o.separate ⟨p.geo.B, usedBytes p.geo.pLen⟩ (by simp [GenerationContext.changed])).sub_right (p.geo.part_sub hh)
  · exact o.separate (below p.geo.F 16) (by simp [GenerationContext.changed])

theorem OutputPlan.packed {p : GenerationContext} (o : OutputPlan p) :
    (p.geo.part packed (2 * p.geo.pLen + p.geo.qLen)).Disjoint ⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ := by
  have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with h | h | h <;> omega
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with h | h <;> omega
  exact ((o.separate _ (by simp [GenerationContext.changed])).sub_right
    (p.geo.part_sub (p.geo.small_bound (by decide) (by unfold arithmeticBytes; omega)))).symm

theorem output_copy_context {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (o : OutputPlan p)
    (hw : (⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ : Region) ∈ s.wr)
    (bs : List Byte) (hlen : bs.length = 2 * p.geo.pLen + p.geo.qLen)
    (bytes : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) = bs) :
    WP isa Impl.Dsa.AArch64.Generation.outputCopy s fun t =>
      t.gpr .x0 = 1 ∧ Spec.Rsa.bytesAt t.mem (p.saved 6) (2 * p.geo.pLen + p.geo.qLen) = bs ∧
      Frame [⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩] s.mem t.mem ∧ Keep (.x0 :: mmRegs) s t := by
  have pn : 2 ≤ p.geo.pLen ∧ p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega
  have bound := p.geo.small_bound (d := packed) (n := 2 * p.geo.pLen + p.geo.qLen)
    (by decide) (by unfold arithmeticBytes; omega)
  have source : Src s (p.saved 6) (2 * p.geo.pLen + p.geo.qLen) (VG.Proof.Bignum.off p.geo.B packed) bs := by
    apply arena_source h.scratch
    · simpa only [hlen] using bound
    · rw [hlen]; omega
    · simpa only [hlen] using bytes
    · simpa only [hlen, GenerationGeometry.part] using o.packed
  have h5 := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
  have h6 := h.slots 6 (by simp [generationSlots])
  have h7 := (h.slots 7 (by simp [generationSlots])).trans o.lengthSlot
  obtain ⟨V, R⟩ := h.rep
  have call := outputCopy_ok h.layout R (by simpa only [hlen] using h7)
    (show 2 ≤ bs.length ∧ bs.length ≤ 1024 by rw [hlen]; omega)
  rw [h5, h6, hlen] at call
  apply call
  · intro i hi; exact source.rd i (hlen ▸ hi)
  · intro i hi; exact ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩
  · intro i hi
    simpa only [VG.Proof.Bignum.off, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hi), Option.getD_some] using source.val i (hlen ▸ hi)
  · intro i hi j hj he
    apply o.packed (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.geo.B packed) i)
      (Offset.contains_base _ (by omega) (by omega))
    rw [he]
    exact Offset.contains_base _ (by omega) (by omega)

end VG.Proof.Dsa.AArch64.Generation
