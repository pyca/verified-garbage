module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedSearchPlanCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NativeGeneratorCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryTape
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorPlan
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryWork
public import Mathlib.Tactic.Push
public import Mathlib.Data.Nat.Basic
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchMemory
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArenaSource
/-! # Public accepted primes determine the generator-search plan -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/GeometryGeneratorWork.lean`, which only this module imported.
section

/-! # Geometry of the generator's parent and arithmetic workspaces -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def GenerationGeometry.gWork (p : GenerationGeometry) : List Region :=
  [p.part arithmetic arithmeticBytes, ⟨p.B, Impl.Dsa.Layout.activeBytes⟩,
    p.part g p.pLen, ⟨p.F, frameBytes⟩]

theorem GenerationGeometry.parentRoom (p : GenerationGeometry) :
    Impl.Dsa.Layout.activeBytes ≤ usedBytes p.pLen := by
  rcases p.width with h | h | h <;> rw [h] <;> decide

theorem GenerationGeometry.gWork_separate (p : GenerationGeometry) {d n : Nat}
    (hd : q ≤ d) (hn : d + n ≤ g) : ∀ r ∈ p.gWork, (p.part d n).Disjoint r := by
  have pn : p.pLen ≤ 384 := by rcases p.width with h | h | h <;> omega
  have hb : d + n ≤ usedBytes p.pLen := by
    have hh := p.small_bound (d := g) (n := 0) (by decide) (by decide)
    omega
  have ha := p.small_bound (d := arithmetic) (n := arithmeticBytes) (by decide) (by rfl)
  have hg := p.small_bound (d := g) (n := p.pLen) (by decide) (by unfold arithmeticBytes; omega)
  intro r hr
  simp only [gWork, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact p.parts_disjoint hb ha (Or.inl (by unfold g arithmetic at *; omega))
  · simpa [GenerationGeometry.part, VG.Proof.Bignum.off] using
      p.parts_disjoint hb (e := 0) (k := Impl.Dsa.Layout.activeBytes) (by simpa using p.parentRoom)
        (Or.inr (by unfold q Impl.Dsa.Layout.activeBytes at *; omega))
  · exact p.parts_disjoint hb hg (Or.inl hn)
  · exact (p.frame_part hb).symm

theorem GenerationTape.gWork {p : GenerationGeometry} (t : GenerationTape p) :
    ∀ r ∈ p.gWork, (⟨t.ptr, t.bytes.length⟩ : Region).Disjoint r := by
  have pn : p.pLen ≤ 384 := by rcases p.width with h | h | h <;> omega
  intro r hr
  simp only [GenerationGeometry.gWork, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact t.part (p.small_bound (by decide) (by rfl))
  · simpa [GenerationGeometry.part, VG.Proof.Bignum.off] using
      t.part (d := 0) (n := Impl.Dsa.Layout.activeBytes) (by simpa using p.parentRoom)
  · exact t.part (p.small_bound (by decide) (by unfold arithmeticBytes; omega))
  · exact t.frame

end VG.Proof.Dsa.AArch64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/GeometryGenerator.lean`, which only this module imported.
section

/-! # Concrete generator plan over the saved p and exponent buffers -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def GenerationGeometry.generatorPlan (p : GenerationGeometry) (pb eb : List Byte)
    (hp : pb.length = p.pLen) (he : eb.length = p.pLen)
    (positive : 1 < Spec.Dsa.decodeBE pb) (odd : Spec.Dsa.decodeBE pb % 2 = 1) : GeneratorPlan := by
  have pn : p.pLen ≤ 384 := by rcases p.width with h | h | h <;> omega
  have ha := p.small_bound (d := arithmetic) (n := arithmeticBytes) (by decide) (by rfl)
  have hh := p.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  have hg := p.small_bound (d := g) (n := p.pLen) (by decide) (by unfold arithmeticBytes; omega)
  have parent : 0 + Impl.Dsa.Layout.activeBytes ≤ usedBytes p.pLen := by simpa using p.parentRoom
  have gp : (p.part g p.pLen).Disjoint ⟨p.B, Impl.Dsa.Layout.activeBytes⟩ := by
    simpa [GenerationGeometry.part, VG.Proof.Bignum.off] using p.parts_disjoint hg parent (Or.inr (by decide))
  have ga := p.parts_disjoint hg ha (Or.inl (by unfold g arithmetic; omega))
  have ps := p.gWork_separate (d := VG.Impl.Dsa.Generation.Layout.p) (n := p.pLen)
    (by decide) (by unfold VG.Impl.Dsa.Generation.Layout.p g; omega)
  have es := p.gWork_separate (d := exponent) (n := p.pLen)
    (by decide) (by unfold exponent g; omega)
  refine {
    B := p.B
    A := VG.Proof.Bignum.off p.B arithmetic
    F := p.F
    S := p.hash
    hp := VG.Proof.Bignum.off p.B VG.Impl.Dsa.Generation.Layout.p
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
    · simpa [GenerationGeometry.part, VG.Proof.Bignum.off] using p.frame_part parent
    · exact p.frame_part hg
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact p.parts_disjoint hh ha (Or.inl (by decide))
    · simpa [GenerationGeometry.part, GenerationGeometry.hash, VG.Proof.Bignum.off] using
        p.parts_disjoint hh parent (Or.inr (by decide))
    · exact p.parts_disjoint hh hg (Or.inl (by decide))
  · intro i hi
    exact out_scr gp (Offset.contains_base _ (by omega) (by omega))
  · intro i hi
    exact out_scr ga (Offset.contains_base _ (by omega) (by omega))

end VG.Proof.Dsa.AArch64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/ContextGenerator.lean`, which only this module imported.
section

/-! # Saved p and exponent bytes supply the complete generator search -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

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
    (bp : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = pb)
    (be : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B exponent) p.geo.pLen = eb) :
    GeneratorSearchMemory (p.generatorPlan W pb eb hp he positive odd qval exponentValue) W s := by
  have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega
  have ha := p.geo.small_bound (d := arithmetic) (n := arithmeticBytes) (by decide) (by rfl)
  have parent : 0 + Impl.Dsa.Layout.activeBytes ≤ usedBytes p.geo.pLen := by simpa using p.geo.parentRoom
  have src (d : Nat) (bs : List Byte) (hlen : bs.length = p.geo.pLen)
      (hd : q ≤ d) (hn : d + p.geo.pLen ≤ g)
      (bytes : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B d) p.geo.pLen = bs)
      (work : Addr) (size : Nat) (member : (⟨work, size⟩ : Region) ∈ p.geo.gWork) :
      Src s work size (VG.Proof.Bignum.off p.geo.B d) bs := by
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
    tapeLength := (h.slots 13 (by simp [generationSlots])).trans p.hLengthSlot
    slots := fun _ _ => rfl
    arithmetic := h.scratch.sub (n := arithmeticBytes) ha (by decide)
    parent := ?_
    pArithmetic := src VG.Impl.Dsa.Generation.Layout.p pb hp (by decide)
      (by unfold VG.Impl.Dsa.Generation.Layout.p g; omega) bp (VG.Proof.Bignum.off p.geo.B arithmetic) arithmeticBytes (by simp [GenerationGeometry.gWork, GenerationGeometry.part])
    tapeArithmetic := h.hs.source ha
    eArithmetic := src exponent eb he (by decide) (by unfold exponent g; omega) be (VG.Proof.Bignum.off p.geo.B arithmetic) arithmeticBytes
      (by simp [GenerationGeometry.gWork, GenerationGeometry.part])
    pParent := src VG.Impl.Dsa.Generation.Layout.p pb hp (by decide)
      (by unfold VG.Impl.Dsa.Generation.Layout.p g; omega) bp p.geo.B Impl.Dsa.Layout.activeBytes (by simp [GenerationGeometry.gWork])
    tapeParent := ?_
    eParent := src exponent eb he (by decide) (by unfold exponent g; omega) be p.geo.B Impl.Dsa.Layout.activeBytes
      (by simp [GenerationGeometry.gWork])
    gWrite := ?_ }
  · change Scr s p.geo.B Impl.Dsa.Layout.activeBytes
    simpa [VG.Proof.Bignum.off] using h.scratch.sub parent (by decide : 0 < Impl.Dsa.Layout.activeBytes)
  · change Src s p.geo.B Impl.Dsa.Layout.activeBytes p.hs.ptr p.hs.bytes
    simpa [VG.Proof.Bignum.off] using h.hs.source parent
  · change ∀ i < p.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.geo.B g) i) 1
    intro i hi
    rw [VG.Proof.Bignum.off_off]
    exact h.scratch.region (by
      have := p.geo.small_bound (d := g) (n := p.geo.pLen) (by decide) (by unfold arithmeticBytes; omega)
      omega) (by decide)

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

structure SeedGeneratorPublic where
  seed : SeedPublic
  value : Nat
  domain : VG.Proof.Dsa.Generation.PDomain seed.context.geo.pLen value

def SeedGeneratorPublic.qValue (p : SeedGeneratorPublic) : Nat :=
  Spec.Dsa.qCandidate (8 * p.seed.context.geo.qLen) p.seed.seed.bytes

def SeedGeneratorPublic.plan (p : SeedGeneratorPublic) : GeneratorSearchPlan := by
  have fit : p.value < 256 ^ p.seed.context.geo.pLen := by
    simpa only [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] using p.domain.upper
  have decode := VG.Proof.Dsa.decodeBE_encodeBE fit
  have expFit : (p.value - 1) / p.qValue < 256 ^ p.seed.context.geo.pLen :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)) fit
  exact p.seed.context.generatorPlan (upd p.seed.words 16 (BitVec.ofNat 64 p.seed.used))
    (Spec.Dsa.encodeBE p.seed.context.geo.pLen p.value)
    (Spec.Dsa.encodeBE p.seed.context.geo.pLen ((p.value - 1) / p.qValue))
    (VG.Proof.Dsa.encodeBE_length _ _) (VG.Proof.Dsa.encodeBE_length _ _)
    (by rw [decode]; omega_using [p.domain.large])
    (by rw [decode]; exact p.domain.odd) p.qValue
    (by rw [decode, VG.Proof.Dsa.decodeBE_encodeBE expFit])

def SeedGeneratorBefore (pLen qLen : Nat) (p : SeedGeneratorPublic) (s : State) : Prop :=
  SeedPrimeBefore pLen qLen p.seed s ∧
  Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.seed.context.geo.B VG.Impl.Dsa.Generation.Layout.p) p.seed.context.geo.pLen =
    Spec.Dsa.encodeBE p.seed.context.geo.pLen p.value ∧
  Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.seed.context.geo.B exponent) p.seed.context.geo.pLen =
    Spec.Dsa.encodeBE p.seed.context.geo.pLen ((p.value - 1) / p.qValue)

theorem seedGenerator_start {pLen qLen : Nat} {p : SeedGeneratorPublic} {s : State}
    (h : SeedGeneratorBefore pLen qLen p s) : GeneratorSearchStart pLen p.plan s := by
  obtain ⟨⟨⟨⟨W, hm, h1, h16, h10⟩, _, _⟩, hp, _⟩, bp, be⟩ := h
  have state := hm.generatorState p.plan.core.pb p.plan.core.eb p.plan.core.pLength p.plan.core.eLength
    p.plan.core.pPositive p.plan.core.pOdd p.qValue p.plan.exponentValue bp be
  refine ⟨⟨W, { state with slots := ?_ }⟩, hp⟩
  intro k hk
  change W k = upd p.seed.words 16 (BitVec.ofNat 64 p.seed.used) k
  by_cases h16k : k = 16
  · subst k; simpa [upd] using h16
  by_cases h1k : k = 1
  · subst k; simpa [upd, SeedPublic.words] using h1
  by_cases h10k : k = 10
  · subst k; simpa [upd, SeedPublic.words] using h10
  have member : k ∈ generationSlots := by
    simp only [generatorSlots, generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
    omega
  simpa [upd, SeedPublic.words, h16k, h1k, h10k] using hm.slots k member

end VG.Proof.Dsa.AArch64.Generation
