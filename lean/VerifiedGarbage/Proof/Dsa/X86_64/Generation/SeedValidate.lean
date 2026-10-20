module
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Validate
public import VerifiedGarbage.Proof.Dsa.X86_64.Parameters
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ArenaSource
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Validate
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork
import VerifiedGarbage.Proof.Dsa.Generation.Memory

/-! # Apply the final domain check without leaving the native seed controller -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem GenerationGeometry.validLengths (p : GenerationGeometry) : Spec.Dsa.lengthsValid p.pLen p.qLen := by
  rcases p.lengths with h | h | h <;> simp [Spec.Dsa.lengthsValid, h.1, h.2]

def GenerationGeometry.parametersInput (p : GenerationGeometry) (params : List Byte)
    (hlen : params.length = 2 * p.pLen + p.qLen) : ParametersInput :=
  ⟨off p.B domainCheck, p.pLen, p.qLen, params, p.validLengths, hlen⟩

theorem seedValidate_ok (M : Mont) (Sq : MontS)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (params : List Byte) (hlen : params.length = 2 * p.geo.pLen + p.geo.qLen)
    (bytes : Spec.Rsa.bytesAt s.mem (off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) = params) :
    WP isa (Impl.Dsa.X86_64.Generation.validate Sq.mm M.mm p.geo.pLen p.geo.qLen) s fun t =>
      GenerationMemory p (upd W 19 (BitVec.ofNat 64
        (if Spec.Dsa.checkParametersBytes p.geo.pLen p.geo.qLen params then 1 else 3))) t ∧
      Spec.Rsa.bytesAt t.mem (off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) = params ∧
      Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega
  have h5 := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
  have arena : domainCheck + Impl.Dsa.Layout.usedBytes ≤ usedBytes p.geo.pLen := by
    rcases p.geo.width with hh | hh | hh <;> rw [hh] <;> decide
  have packedBound := p.geo.small_bound (d := packed) (n := 2 * p.geo.pLen + p.geo.qLen)
    (by decide) (by unfold arithmeticBytes; omega)
  have hh := p.geo.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  have sep := p.geo.parts_disjoint packedBound arena (Or.inl (by unfold packed domainCheck; omega))
  have source : Src s (off p.geo.B domainCheck) Impl.Dsa.Layout.usedBytes (off p.geo.B packed) params := by
    apply arena_source h.scratch
    · simpa only [hlen] using packedBound
    · rw [hlen]; omega
    · simpa only [hlen] using bytes
    · simpa only [hlen, GenerationGeometry.part] using sep
  obtain ⟨V, R⟩ := h.rep
  have call := validate_ok M Sq (p.geo.parametersInput params hlen) h.layout R
    (by change off p.geo.B domainCheck = off (W 5) domainCheck; rw [h5])
    (by change p.geo.pLen < 2 ^ 32; omega) (by change p.geo.qLen < 2 ^ 32; omega)
    (h.scratch.sub (n := Impl.Dsa.Layout.usedBytes) arena (by decide))
  rw [h5] at call
  refine WP.mono (call source (p.geo.frame_part arena) (p.geo.parts_disjoint hh arena (Or.inl (by decide))))
    fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  have ff : Frame p.changed s.mem t.mem := by
    apply GenerationContext.frame_parts ft
    intro r hr
    change r ∈ [⟨off p.geo.B domainCheck, Impl.Dsa.Layout.usedBytes⟩, ⟨p.geo.F, frameBytes⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨p.geo.B, usedBytes p.geo.pLen⟩, by simp [GenerationContext.changed], p.geo.part_sub arena⟩
    · exact ⟨⟨p.geo.F, frameBytes⟩, by simp [GenerationContext.changed], fun _ h => h⟩
  refine ⟨h.frame Lt ⟨V, Rt⟩ ?_ ff kt.2.1 kt.2.2, ?_, ff, kt.2.1, kt.2.2⟩
  · intro k hk
    have hn : k ≠ 19 := by simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; omega
    simp [upd, hn]
  · rw [VG.Proof.Dsa.Generation.frame_bytesAt ft (by
      intro r hr
      change r ∈ [⟨off p.geo.B domainCheck, Impl.Dsa.Layout.usedBytes⟩, ⟨p.geo.F, frameBytes⟩] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sep
      · exact (p.geo.frame_part packedBound).symm) (by omega)]
    exact bytes

end VG.Proof.Dsa.X86_64.Generation
