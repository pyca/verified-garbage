module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
public import Mathlib.Tactic.Conv
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedSearch
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory

/-! # Phase dispatch retains the complete generation state -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64

theorem GenerationMemory.congr {p : GenerationContext} {W : Nat → BitVec 64} {s t : State}
    (h : GenerationMemory p W s) (hm : t.mem = s.mem) (hk : Keep [.rax] s t) : GenerationMemory p W t := by
  obtain ⟨V, R⟩ := h.rep
  have Rt : Rep t.mem p.geo.F p.geo.hash V W := hm ▸ R
  have Lt := lay_of_rep h.layout R Rt rfl (hk.gpr (by decide)) hk.2.2
  exact h.frame Lt ⟨V, Rt⟩ (fun _ _ => rfl) (by rw [hm]; exact Frame.refl _ _) hk.2.1 hk.2.2

theorem onSuccess_generation_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    {next : Prog isa} {Q : State → Prop} (h : GenerationMemory p W s)
    (accepted : ∀ t, GenerationMemory p W t → t.mem = s.mem → Keep [.rax] s t → W 19 = 1 → WP isa next t Q)
    (rejected : ∀ t, GenerationMemory p W t → t.mem = s.mem → Keep [.rax] s t → W 19 ≠ 1 → Q t) :
    WP isa (Impl.Dsa.X86_64.Generation.onSuccess next) s Q := by
  obtain ⟨V, R⟩ := h.rep
  exact onSuccess_ok h.layout R
    (fun t hm hk hs => accepted t (h.congr hm hk) hm hk hs)
    (fun t hm hk hs => rejected t (h.congr hm hk) hm hk hs)

end VG.Proof.Dsa.X86_64.Generation
