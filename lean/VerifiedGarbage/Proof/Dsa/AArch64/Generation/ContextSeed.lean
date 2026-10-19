module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextFrame
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedArguments
import VerifiedGarbage.Proof.Framework.Omega

/-! # Prepare q hashing while retaining all persistent search inputs -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem prepareSeed_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.seedArguments p.geo.qLen)) s fun t =>
      GenerationMemory p (seedWords W p.geo.qLen) t ∧ Frame p.changed s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  obtain ⟨V, R⟩ := h.rep
  refine WP.mono (seedArguments_ok h.layout R (by rcases p.geo.qWidth with hh | hh <;> omega))
    fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  have ff := GenerationContext.frame_single (p := p) ft
  refine ⟨h.frame Lt ⟨V, Rt⟩ ?_ ff kt.rd kt.wr, ff, kt⟩
  intro k hk
  simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rfl
    | simpa [seedWords, upd] using ((h.slots 26 (by simp [generationSlots])).trans p.hashLenSlot).symm

end VG.Proof.Dsa.AArch64.Generation
