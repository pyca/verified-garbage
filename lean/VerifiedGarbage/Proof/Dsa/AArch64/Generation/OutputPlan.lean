module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecOut
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Output
public import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OutputArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CopyBytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArenaSource
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryWork
import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Table
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ToDual

/-! ### `Dsa.AArch64.Generation.OutputCopy`, which only this module used -/

section

/-! # Copy accepted packed parameters to the caller and return success -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem outputCopy_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} {bs : List Byte}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hlen : W 7 = BitVec.ofNat 64 bs.length)
    (hl : 2 ≤ bs.length ∧ bs.length ≤ 1024)
    (hrd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) packed) i) 1)
    (hwr : ∀ i < bs.length, InRegions s.wr (VG.Proof.Bignum.off (W 6) i) 1)
    (hb : ∀ i < bs.length, s.mem (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) packed) i) = bs.getD i 0)
    (sep : ∀ i < bs.length, ∀ j < bs.length, VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) packed) i ≠ VG.Proof.Bignum.off (W 6) j) :
    WP isa Impl.Dsa.AArch64.Generation.outputCopy s fun t =>
      t.gpr .x0 = 1 ∧ Spec.Rsa.bytesAt t.mem (W 6) bs.length = bs ∧
      Frame [⟨W 6, bs.length⟩] s.mem t.mem ∧ Keep (.x0 :: mmRegs) s t := by
  unfold Impl.Dsa.AArch64.Generation.outputCopy
  refine WP.seq (WP.mono (outputArgs_ok L R hlen) fun u ⟨hsi, hdi, hcx, hm, ku⟩ => ?_)
  refine WP.seq (WP.mono (copyBytes_ok (by omega_using [hl]) hsi hdi hcx
    (fun i hi => by rw [ku.rd, ku.wr]; exact hrd i hi)
    (fun i hi => by rw [ku.wr]; exact hwr i hi)
    (fun i hi => by rw [hm]; exact hb i hi) sep) fun v ⟨bytes, fv, kv⟩ => ?_)
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 1 ∧ t.mem = v.mem)
    (by brun) rfl rfl rfl) fun t ⟨⟨hr, hmem⟩, kt⟩ => ?_
  refine ⟨hr, hmem ▸ bytes, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  intro a ha
  rw [hmem, fv a (by
    intro i hi he
    apply ha ⟨W 6, bs.length⟩ (by simp)
    rw [he]
    exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hl, hi])), hm]

end VG.Proof.Dsa.AArch64.Generation

end

end


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
  · exact (o.separate (below p.geo.F 272) (by simp [GenerationContext.changed])).sub_right
      (below_sub (a := 16) (by decide) (by decide))

theorem OutputPlan.packed {p : GenerationContext} (o : OutputPlan p) :
    (p.geo.part packed (2 * p.geo.pLen + p.geo.qLen)).Disjoint ⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ := by
  have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with h | h | h <;> omega_using [h]
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with h | h <;> omega_using [h]
  exact ((o.separate _ (by simp [GenerationContext.changed])).sub_right
    (p.geo.part_sub (p.geo.small_bound (by decide) (by unfold arithmeticBytes; omega_using [pn, qn])))).symm

theorem output_copy_context {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (o : OutputPlan p)
    (hw : (⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ : Region) ∈ s.wr)
    (bs : List Byte) (hlen : bs.length = 2 * p.geo.pLen + p.geo.qLen)
    (bytes : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) = bs) :
    WP isa Impl.Dsa.AArch64.Generation.outputCopy s fun t =>
      t.gpr .x0 = 1 ∧ Spec.Rsa.bytesAt t.mem (p.saved 6) (2 * p.geo.pLen + p.geo.qLen) = bs ∧
      Frame [⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩] s.mem t.mem ∧ Keep (.x0 :: mmRegs) s t := by
  have pn : 2 ≤ p.geo.pLen ∧ p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega_using [hh]
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega_using [hh]
  have bound := p.geo.small_bound (d := packed) (n := 2 * p.geo.pLen + p.geo.qLen)
    (by decide) (by unfold arithmeticBytes; omega_using [pn, qn])
  have source : Src s (p.saved 6) (2 * p.geo.pLen + p.geo.qLen) (VG.Proof.Bignum.off p.geo.B packed) bs := by
    apply arena_source h.scratch
    · simpa only [hlen] using bound
    · rw [hlen]; omega_using [pn, qn]
    · simpa only [hlen] using bytes
    · simpa only [hlen, GenerationGeometry.part] using o.packed
  have h5 := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
  have h6 := h.slots 6 (by simp [generationSlots])
  have h7 := (h.slots 7 (by simp [generationSlots])).trans o.lengthSlot
  obtain ⟨V, R⟩ := h.rep
  have call := outputCopy_ok h.layout R (by simpa only [hlen] using h7)
    (show 2 ≤ bs.length ∧ bs.length ≤ 1024 by rw [hlen]; omega_using [pn, qn])
  rw [h5, h6, hlen] at call
  apply call
  · intro i hi; exact source.rd i (hlen ▸ hi)
  · intro i hi; exact ⟨_, hw, Offset.contains_base _ (by omega_using [hi]) (by omega_using [pn, qn, hi])⟩
  · intro i hi
    simpa only [VG.Proof.Bignum.off, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hi), Option.getD_some] using source.val i (hlen ▸ hi)
  · intro i hi j hj he
    apply o.packed (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.geo.B packed) i)
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [pn, qn, hi]))
    rw [he]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [pn, qn, hj])

end VG.Proof.Dsa.AArch64.Generation
