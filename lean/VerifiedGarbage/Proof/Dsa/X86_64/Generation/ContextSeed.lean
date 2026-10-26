module

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedArguments
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-! # Prepare q hashing while retaining all persistent search inputs -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem prepareSeed_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.seedArguments p.geo.qLen)) s fun t =>
      GenerationMemory p (seedWords W p.geo.qLen) t ∧ Frame p.changed s.mem t.mem ∧ Keep [.rax] s t := by
  obtain ⟨V, R⟩ := h.rep
  refine WP.mono (seedArguments_ok h.layout R (by rcases p.geo.qWidth with hh | hh <;> omega))
    fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  have ff := GenerationContext.frame_single (p := p) ft
  refine ⟨h.frame Lt ⟨V, Rt⟩ ?_ ff kt.2.1 kt.2.2, ff, kt⟩
  intro k hk
  simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rfl
    | simpa [seedWords, upd] using ((h.slots 28 (by simp [generationSlots])).trans p.hashLenSlot).symm

end VG.Proof.Dsa.X86_64.Generation
