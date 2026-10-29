module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorSearchMemory
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryGeneratorWork
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorPlan
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork
public import Mathlib.Tactic.Push
public import Mathlib.Data.Nat.Basic
public import Mathlib.Algebra.Group.Monoid
public import VerifiedGarbage.Proof.Bignum.Octets

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ArenaSource
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import Mathlib.Tactic.ToAdditive
/-! # Saved p and exponent bytes supply the complete generator search -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/GeometryGenerator.lean`, which only this module imported.
section

/-! # Concrete generator plan over the saved p and exponent buffers -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def GenerationGeometry.generatorPlan (p : GenerationGeometry) (pb eb : List Byte)
    (hp : pb.length = p.pLen) (he : eb.length = p.pLen)
    (positive : 1 < Spec.Dsa.decodeBE pb) (odd : Spec.Dsa.decodeBE pb % 2 = 1) : GeneratorPlan := by
  have pn : p.pLen ≤ 384 := by rcases p.width with h | h | h <;> omega
  have ha := p.small_bound (d := arithmetic) (n := arithmeticBytes) (by decide) (by rfl)
  have hh := p.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  have hg := p.small_bound (d := g) (n := p.pLen) (by decide) (by unfold arithmeticBytes; omega)
  have parent : 0 + Impl.Dsa.Layout.activeBytes ≤ usedBytes p.pLen := by simpa using p.parentRoom
  have gp : (p.part g p.pLen).Disjoint ⟨p.B, Impl.Dsa.Layout.activeBytes⟩ := by
    simpa [GenerationGeometry.part, off] using p.parts_disjoint hg parent (Or.inr (by decide))
  have ga := p.parts_disjoint hg ha (Or.inl (by unfold g arithmetic; omega))
  have ps := p.gWork_separate (d := VG.Impl.Dsa.Generation.Layout.p) (n := p.pLen)
    (by decide) (by unfold VG.Impl.Dsa.Generation.Layout.p g; omega)
  have es := p.gWork_separate (d := exponent) (n := p.pLen)
    (by decide) (by unfold exponent g; omega)
  refine {
    B := p.B
    A := off p.B arithmetic
    F := p.F
    S := p.hash
    hp := off p.B VG.Impl.Dsa.Generation.Layout.p
    Z := arithmeticBytes
    len := p.pLen
    pb := pb
    hb := pb
    eb := eb
    width := p.width
    arithmeticBase := rfl
    workspaceRoom := by rcases p.width with h | h | h <;> rw [h] <;> decide
    pLength := hp
    hLength := hp
    eLength := he
    pPositive := positive
    pOdd := odd
    frameHeaders := p.frame_headers
    frameOutside := p.frame_outside
    frameSeparate := ?_
    hashSeparate := ?_
    pSeparate := ps
    hSeparate := ps
    eSeparate := es
    gArithmeticSeparate := ga
    gParentOutside := ?_
    gArithmeticOutside := ?_ }
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact p.frame_part ha
    · simpa [GenerationGeometry.part, off] using p.frame_part parent
    · exact p.frame_part hg
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact p.parts_disjoint hh ha (Or.inl (by decide))
    · simpa [GenerationGeometry.part, GenerationGeometry.hash, off] using
        p.parts_disjoint hh parent (Or.inr (by decide))
    · exact p.parts_disjoint hh hg (Or.inl (by decide))
  · intro i hi
    exact out_scr gp (Offset.contains_base _ (by omega) (by omega))
  · intro i hi
    exact out_scr ga (Offset.contains_base _ (by omega) (by omega))

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def GenerationContext.generatorPlan (p : GenerationContext) (W : Nat → BitVec 64)
    (pb eb : List Byte) (hp : pb.length = p.geo.pLen) (he : eb.length = p.geo.pLen)
    (positive : 1 < Spec.Dsa.decodeBE pb) (odd : Spec.Dsa.decodeBE pb % 2 = 1)
    (qval : Nat) (exponentValue : Spec.Dsa.decodeBE eb = (Spec.Dsa.decodeBE pb - 1) / qval) : GeneratorSearchPlan where
  core := p.geo.generatorPlan pb eb hp he positive odd
  saved := W
  tape := p.hs.bytes
  tapePtr := p.hs.ptr
  tapeFits := p.hs.size
  tapeSeparate := p.hs.gWork
  q := qval
  exponentValue := exponentValue

theorem GenerationMemory.generatorState {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (pb eb : List Byte)
    (hp : pb.length = p.geo.pLen) (he : eb.length = p.geo.pLen)
    (positive : 1 < Spec.Dsa.decodeBE pb) (odd : Spec.Dsa.decodeBE pb % 2 = 1)
    (qval : Nat) (exponentValue : Spec.Dsa.decodeBE eb = (Spec.Dsa.decodeBE pb - 1) / qval)
    (bp : Spec.Rsa.bytesAt s.mem (off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = pb)
    (be : Spec.Rsa.bytesAt s.mem (off p.geo.B exponent) p.geo.pLen = eb) :
    GeneratorSearchMemory (p.generatorPlan W pb eb hp he positive odd qval exponentValue) W s := by
  have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega
  have ha := p.geo.small_bound (d := arithmetic) (n := arithmeticBytes) (by decide) (by rfl)
  have parent : 0 + Impl.Dsa.Layout.activeBytes ≤ usedBytes p.geo.pLen := by simpa using p.geo.parentRoom
  have src (d : Nat) (bs : List Byte) (hlen : bs.length = p.geo.pLen)
      (hd : q ≤ d) (hn : d + p.geo.pLen ≤ g)
      (bytes : Spec.Rsa.bytesAt s.mem (off p.geo.B d) p.geo.pLen = bs)
      (work : Addr) (size : Nat) (member : (⟨work, size⟩ : Region) ∈ p.geo.gWork) :
      Src s work size (off p.geo.B d) bs := by
    apply arena_source h.scratch
    · rw [hlen]
      have bound := p.geo.small_bound (d := g) (n := 0) (by decide) (by decide)
      omega
    · rw [hlen]; omega
    · simpa only [hlen] using bytes
    · simpa only [hlen, GenerationGeometry.part] using p.geo.gWork_separate hd hn _ member
  refine {
    layout := h.layout
    rep := h.rep
    base := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
    tapeBase := (h.slots 11 (by simp [generationSlots])).trans p.hSlot
    tapeLength := (h.slots 12 (by simp [generationSlots])).trans p.hLengthSlot
    slots := fun _ _ => rfl
    arithmetic := h.scratch.sub (n := arithmeticBytes) ha (by decide)
    parent := ?_
    pArithmetic := src VG.Impl.Dsa.Generation.Layout.p pb hp (by decide)
      (by unfold VG.Impl.Dsa.Generation.Layout.p g; omega) bp (off p.geo.B arithmetic) arithmeticBytes (by simp [GenerationGeometry.gWork, GenerationGeometry.part])
    tapeArithmetic := h.hs.source ha
    eArithmetic := src exponent eb he (by decide) (by unfold exponent g; omega) be (off p.geo.B arithmetic) arithmeticBytes
      (by simp [GenerationGeometry.gWork, GenerationGeometry.part])
    pParent := src VG.Impl.Dsa.Generation.Layout.p pb hp (by decide)
      (by unfold VG.Impl.Dsa.Generation.Layout.p g; omega) bp p.geo.B Impl.Dsa.Layout.activeBytes (by simp [GenerationGeometry.gWork])
    tapeParent := ?_
    eParent := src exponent eb he (by decide) (by unfold exponent g; omega) be p.geo.B Impl.Dsa.Layout.activeBytes
      (by simp [GenerationGeometry.gWork])
    gWrite := ?_ }
  · change Scr s p.geo.B Impl.Dsa.Layout.activeBytes
    simpa [off] using h.scratch.sub parent (by decide : 0 < Impl.Dsa.Layout.activeBytes)
  · change Src s p.geo.B Impl.Dsa.Layout.activeBytes p.hs.ptr p.hs.bytes
    simpa [off] using h.hs.source parent
  · change ∀ i < p.geo.pLen, InRegions s.wr (off (off p.geo.B g) i) 1
    intro i hi
    rw [off_off]
    exact h.scratch.region (by
      have := p.geo.small_bound (d := g) (n := p.geo.pLen) (by decide) (by unfold arithmeticBytes; omega)
      omega) (by decide)

end VG.Proof.Dsa.X86_64.Generation
