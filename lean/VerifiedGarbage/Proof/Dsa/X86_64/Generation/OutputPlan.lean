module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Output
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Out
public import Mathlib.Algebra.Group.Nat.Defs
public import Aesop.BuiltinRules

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ArenaSource
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OutputArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyDigest
/-! # The caller's output is disjoint from every parameter-search workspace -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/OutputCopy.lean`, which only this module imported.
section

/-! # Copy accepted packed parameters to the caller and return success -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem outputCopy_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} {bs : List Byte}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hlen : W 7 = BitVec.ofNat 64 bs.length)
    (hl : 2 ≤ bs.length ∧ bs.length ≤ 1024)
    (hrd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (off (off (W 5) packed) i) 1)
    (hwr : ∀ i < bs.length, InRegions s.wr (off (W 6) i) 1)
    (hb : ∀ i < bs.length, s.mem (off (off (W 5) packed) i) = bs.getD i 0)
    (sep : ∀ i < bs.length, ∀ j < bs.length, off (off (W 5) packed) i ≠ off (W 6) j) :
    WP isa Impl.Dsa.X86_64.Generation.outputCopy s fun t =>
      t.gpr .rax = 1 ∧ Spec.Rsa.bytesAt t.mem (W 6) bs.length = bs ∧
      Frame [⟨W 6, bs.length⟩] s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  unfold Impl.Dsa.X86_64.Generation.outputCopy
  refine WP.seq (WP.mono (outputArgs_ok L R hlen) fun u ⟨hsi, hdi, hcx, hdx, hm, ku⟩ => ?_)
  refine WP.seq (WP.mono (copyBytes_ok hl hsi hdi hcx hdx
    (fun i hi => by rw [ku.2.1, ku.2.2]; exact hrd i hi)
    (fun i hi => by rw [ku.2.2]; exact hwr i hi)
    (fun i hi => by rw [hm]; exact hb i hi) sep) fun v ⟨bytes, fv, kv⟩ => ?_)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = 1 ∧ t.mem = v.mem)
    (by xrun) rfl) fun t ⟨⟨hr, hmem⟩, kt⟩ => ?_
  refine ⟨hr, hmem ▸ bytes, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  intro a ha
  rw [hmem, fv a (by
    intro i hi he
    apply ha ⟨W 6, bs.length⟩ (by simp)
    rw [he]
    exact Offset.contains_base _ (by omega) (by omega)), hm]

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

structure OutputPlan (p : GenerationContext) : Prop where
  lengthSlot : p.saved 7 = BitVec.ofNat 64 (2 * p.geo.pLen + p.geo.qLen)
  bound : (p.saved 6).toNat + (2 * p.geo.pLen + p.geo.qLen) ≤ 2 ^ 64
  separate : ∀ r ∈ p.changed, (⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ : Region).Disjoint r

theorem OutputPlan.apart {p : GenerationContext} (o : OutputPlan p) :
    Apart p.geo.F p.geo.hash ⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ := by
  have hh := p.geo.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  refine ⟨(o.separate _ (by simp [GenerationContext.changed])).symm, ?_, ?_⟩
  · exact ((o.separate _ (by simp [GenerationContext.changed])).sub_right (p.geo.part_sub hh)).symm
  · exact ((o.separate (below p.geo.F 192) (by simp [GenerationContext.changed])).sub_right (below_sub (a := 16) (by decide) (by decide))).symm

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
    (bytes : Spec.Rsa.bytesAt s.mem (off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) = bs) :
    WP isa Impl.Dsa.X86_64.Generation.outputCopy s fun t =>
      t.gpr .rax = 1 ∧ Spec.Rsa.bytesAt t.mem (p.saved 6) (2 * p.geo.pLen + p.geo.qLen) = bs ∧
      Frame [⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩] s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  have pn : 2 ≤ p.geo.pLen ∧ p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega
  have bound := p.geo.small_bound (d := packed) (n := 2 * p.geo.pLen + p.geo.qLen)
    (by decide) (by unfold arithmeticBytes; omega)
  have source : Src s (p.saved 6) (2 * p.geo.pLen + p.geo.qLen) (off p.geo.B packed) bs := by
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
    simpa only [off, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hi), Option.getD_some] using source.val i (hlen ▸ hi)
  · intro i hi j hj he
    apply o.packed (off (off p.geo.B packed) i)
      (Offset.contains_base _ (by omega) (by omega))
    rw [he]
    exact Offset.contains_base _ (by omega) (by omega)

end VG.Proof.Dsa.X86_64.Generation
