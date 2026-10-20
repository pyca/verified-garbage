module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ValidateCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedValidate
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PackMemoryCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArenaSource
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryWork

/-! # Final domain validation uses the generation arena and exact packed bytes -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.Generation.Layout VG.Impl.RsaOaep.AArch64

structure ValidationContext where
  context : GenerationContext
  params : List Byte
  length : params.length = 2 * context.geo.pLen + context.geo.qLen

theorem GenerationGeometry.validationRoom (p : GenerationGeometry) :
    domainCheck + Impl.Dsa.Layout.usedBytes ≤ usedBytes p.pLen := by
  rcases p.width with h | h | h <;> rw [h] <;> decide

def ValidationContext.plan (p : ValidationContext) : ValidatePublic where
  input := p.context.geo.parametersInput p.params p.length
  B := p.context.geo.B
  F := p.context.geo.F
  S := p.context.geo.hash
  base := rfl
  frame := p.context.geo.frame_part p.context.geo.validationRoom
  hash := p.context.geo.parts_disjoint
    (p.context.geo.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide))
    p.context.geo.validationRoom (Or.inl (by decide))

def SeedValidateBefore (pLen qLen : Nat) (p : ValidationContext) (s : State) : Prop :=
  GenerationMemoryBefore p.context s ∧
  Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.context.geo.B packed) (2 * p.context.geo.pLen + p.context.geo.qLen) = p.params ∧
  p.context.geo.pLen = pLen ∧ p.context.geo.qLen = qLen

theorem seedValidate_before {pLen qLen : Nat} {p : ValidationContext} {s : State}
    (h : SeedValidateBefore pLen qLen p s) : ValidateBefore pLen qLen p.plan s := by
  obtain ⟨⟨W, hm⟩, bytes, hp, hq⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  have pn : p.context.geo.pLen ≤ 384 := by rcases p.context.geo.width with hh | hh | hh <;> omega
  have qn : p.context.geo.qLen ≤ 32 := by rcases p.context.geo.qWidth with hh | hh <;> omega
  have packedBound := p.context.geo.small_bound (d := packed)
    (n := 2 * p.context.geo.pLen + p.context.geo.qLen) (by decide) (by unfold arithmeticBytes; omega)
  have sep := p.context.geo.parts_disjoint packedBound p.context.geo.validationRoom
    (Or.inl (by unfold packed domainCheck; omega))
  have source : Src s (VG.Proof.Bignum.off p.context.geo.B domainCheck) Impl.Dsa.Layout.usedBytes
      (VG.Proof.Bignum.off p.context.geo.B packed) p.params := by
    apply arena_source hm.scratch
    · simpa only [p.length] using packedBound
    · rw [p.length]; omega
    · simpa only [p.length] using bytes
    · simpa only [p.length, GenerationGeometry.part] using sep
  exact ⟨hm.layout, ⟨V, W, R, (hm.slots 5 (by simp [generationSlots])).trans p.context.baseSlot⟩,
    hm.scratch.sub p.context.geo.validationRoom (by decide), source, hp, hq⟩

theorem seedValidate_ct (M : Mont)  (pLen qLen : Nat)
    (sizes : (pLen = 128 ∧ qLen = 20) ∨ (pLen = 256 ∧ qLen = 32) ∨ (pLen = 384 ∧ qLen = 32)) :
    RelCT isa (Two (SeedValidateBefore pLen qLen))
      (Impl.Dsa.AArch64.Generation.validate M.mm pLen qLen) (fun _ _ => True) :=
  two_map ValidationContext.plan (fun _ _ h => seedValidate_before h) (validate_ct M pLen qLen sizes)

end VG.Proof.Dsa.AArch64.Generation
