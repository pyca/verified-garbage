module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OnSuccess

/-! # Phase dispatch retains the complete generation state -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64

theorem GenerationMemory.congr {p : GenerationContext} {W : Nat → BitVec 64} {s t : State}
    (h : GenerationMemory p W s) (hm : t.mem = s.mem) (hk : Keep [.x3, .x4] s t) : GenerationMemory p W t := by
  obtain ⟨V, R⟩ := h.rep
  have Rt : Rep t.mem p.geo.F p.geo.hash V W := hm ▸ R
  have Lt := lay_of_rep h.layout R Rt rfl hk.sp hk.wr
  exact h.frame Lt ⟨V, Rt⟩ (fun _ _ => rfl) (by rw [hm]; exact Frame.refl _ _) hk.rd hk.wr

theorem onSuccess_generation_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    {next : Prog isa} {Q : State → Prop} (h : GenerationMemory p W s)
    (accepted : ∀ t, GenerationMemory p W t → t.mem = s.mem → Keep [.x3, .x4] s t → W 19 = 1 → WP isa next t Q)
    (rejected : ∀ t, GenerationMemory p W t → t.mem = s.mem → Keep [.x3, .x4] s t → W 19 ≠ 1 → Q t) :
    WP isa (Impl.Dsa.AArch64.Generation.onSuccess next) s Q := by
  obtain ⟨V, R⟩ := h.rep
  exact onSuccess_ok h.layout R
    (fun t hm hk hs => accepted t (h.congr hm hk) hm hk hs)
    (fun t hm hk hs => rejected t (h.congr hm hk) hm hk hs)

end VG.Proof.Dsa.AArch64.Generation
