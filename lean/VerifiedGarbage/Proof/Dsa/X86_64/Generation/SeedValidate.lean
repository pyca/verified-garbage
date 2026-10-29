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
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ValidateCore
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
/-! # Apply the final domain check without leaving the native seed controller -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/Validate.lean`, which only this module imported.
section

/-! # Domain-check results control native seed retry or acceptance -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout


variable {checkName : String}

theorem validate_ok (M : Mont) (Sq : MontS) {s : State} {F S : Addr}
    {V : Nat → Byte} {W : Nat → BitVec 64} (p : ParametersInput)
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (hbase : p.base = off (W 5) domainCheck)
    (hp : p.pLen < 2 ^ 32) (hq : p.qLen < 2 ^ 32)
    (hs : Scr s p.base Impl.Dsa.Layout.usedBytes)
    (src : Src s p.base Impl.Dsa.Layout.usedBytes (off (W 5) packed) p.params)
    (hF : (⟨F, frameBytes⟩ : Region).Disjoint ⟨p.base, Impl.Dsa.Layout.usedBytes⟩)
    (hS : (⟨S, oRsa⟩ : Region).Disjoint ⟨p.base, Impl.Dsa.Layout.usedBytes⟩)
    (hstack : (below F 8).Disjoint ⟨p.base, Impl.Dsa.Layout.usedBytes⟩)
    (hparams : (below F 8).Disjoint ⟨off (W 5) packed, p.params.length⟩) :
    WP isa (Impl.Dsa.X86_64.Generation.validate (checkName := checkName) Sq.mm M.mm p.pLen p.qLen) s fun t =>
      Lay t F S ∧ Rep t.mem F S V
        (upd W 19 (BitVec.ofNat 64 (if Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params then 1 else 3))) ∧
      Frame [⟨p.base, Impl.Dsa.Layout.usedBytes⟩, below F 8, ⟨F, frameBytes⟩] s.mem t.mem ∧ Keep coreRegs s t := by
  unfold Impl.Dsa.X86_64.Generation.validate
  refine WP.seq (WP.mono (validateCore_ok (checkName := checkName) M Sq p L R hbase hp hq hs src hF hS hstack hparams)
    fun u ⟨hr, Lu, Ru, fu, ku⟩ => ?_)
  refine WP.seq (WP.mono (validateTest_ok hr) fun v ⟨hz, hm, kv⟩ => ?_)
  have Rv : Rep v.mem F S V W := hm ▸ Ru
  have Lv := lay_of_rep Lu Ru Rv rfl (kv.gpr (by decide)) kv.2.2
  have fv : Frame [⟨p.base, Impl.Dsa.Layout.usedBytes⟩, below F 8, ⟨F, frameBytes⟩] s.mem v.mem := by
    rw [hm]
    exact fu.mono (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp)
  have finish (status : Nat) (hstatus : status < 2 ^ 32) :
      WP isa (.block (Impl.Dsa.X86_64.Generation.stackStatus status)) v fun t =>
        Lay t F S ∧ Rep t.mem F S V (upd W 19 (BitVec.ofNat 64 status)) ∧
        Frame [⟨p.base, Impl.Dsa.Layout.usedBytes⟩, below F 8, ⟨F, frameBytes⟩] s.mem t.mem ∧ Keep coreRegs s t := by
    refine WP.mono (stackStatus_ok Lv Rv status hstatus) fun t ⟨Lt, Rt, ft, kt⟩ => ?_
    refine ⟨Lt, Rt, fv.trans ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
    intro a ha
    apply ft a
    right
    have hn := ha ⟨F, frameBytes⟩ (by simp)
    change ¬ ofs F a < frameBytes at hn
    unfold frameBytes at hn
    omega
  cases hc : Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params with
  | false =>
    refine WP.ite true (by simp [eval, hz, hc]) (fun _ => ?_) (fun he => Bool.noConfusion he)
    simpa only [hc, Bool.false_eq_true, ite_false] using finish 3 (by decide)
  | true =>
    refine WP.ite false (by simp [eval, hz, hc]) (fun he => Bool.noConfusion he) (fun _ => ?_)
    simpa only [hc, ite_true] using finish 1 (by decide)

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout


variable {checkName : String}

theorem GenerationGeometry.validLengths (p : GenerationGeometry) : Spec.Dsa.lengthsValid p.pLen p.qLen := by
  rcases p.lengths with h | h | h <;> simp [Spec.Dsa.lengthsValid, h.1, h.2]

def GenerationGeometry.parametersInput (p : GenerationGeometry) (params : List Byte)
    (hlen : params.length = 2 * p.pLen + p.qLen) : ParametersInput :=
  ⟨off p.B domainCheck, p.pLen, p.qLen, params, p.validLengths, hlen⟩

theorem seedValidate_ok (M : Mont) (Sq : MontS)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (params : List Byte) (hlen : params.length = 2 * p.geo.pLen + p.geo.qLen)
    (bytes : Spec.Rsa.bytesAt s.mem (off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) = params) :
    WP isa (Impl.Dsa.X86_64.Generation.validate (checkName := checkName) Sq.mm M.mm p.geo.pLen p.geo.qLen) s fun t =>
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
  have call := validate_ok (checkName := checkName) M Sq (p.geo.parametersInput params hlen) h.layout R
    (by change off p.geo.B domainCheck = off (W 5) domainCheck; rw [h5])
    (by change p.geo.pLen < 2 ^ 32; omega) (by change p.geo.qLen < 2 ^ 32; omega)
    (h.scratch.sub (n := Impl.Dsa.Layout.usedBytes) arena (by decide))
  rw [h5] at call
  refine WP.mono (call source (p.geo.frame_part arena) (p.geo.parts_disjoint hh arena (Or.inl (by decide)))
    ((p.geo.stack_part arena).sub_left (below_sub (by decide) (by decide)))
    (by change (below p.geo.F 8).Disjoint ⟨off p.geo.B packed, params.length⟩
        rw [hlen]
        exact (p.geo.stack_part packedBound).sub_left (below_sub (by decide) (by decide))))
    fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  have ff : Frame p.changed s.mem t.mem := by
    apply GenerationContext.frame_parts ft
    intro r hr
    change r ∈ [⟨off p.geo.B domainCheck, Impl.Dsa.Layout.usedBytes⟩, below p.geo.F 8, ⟨p.geo.F, frameBytes⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨p.geo.B, usedBytes p.geo.pLen⟩, by simp [GenerationContext.changed], p.geo.part_sub arena⟩
    · exact ⟨below p.geo.F 192, by simp [GenerationContext.changed], below_sub (by decide) (by decide)⟩
    · exact ⟨⟨p.geo.F, frameBytes⟩, by simp [GenerationContext.changed], fun _ h => h⟩
  refine ⟨h.frame Lt ⟨V, Rt⟩ ?_ ff kt.2.1 kt.2.2, ?_, ff, kt.2.1, kt.2.2⟩
  · intro k hk
    have hn : k ≠ 19 := by simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; omega
    simp [upd, hn]
  · rw [VG.Proof.Dsa.Generation.frame_bytesAt ft (by
      intro r hr
      change r ∈ [⟨off p.geo.B domainCheck, Impl.Dsa.Layout.usedBytes⟩, below p.geo.F 8, ⟨p.geo.F, frameBytes⟩] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sep
      · exact ((p.geo.stack_part packedBound).sub_left (below_sub (by decide) (by decide))).symm
      · exact (p.geo.frame_part packedBound).symm) (by omega)]
    exact bytes

end VG.Proof.Dsa.X86_64.Generation
