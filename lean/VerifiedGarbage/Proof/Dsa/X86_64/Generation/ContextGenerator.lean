module

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ArenaSource
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryGenerator
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorSearchMemory
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Impl.Sha512.X86_64

/-! # Saved p and exponent bytes supply the complete generator search -/

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
