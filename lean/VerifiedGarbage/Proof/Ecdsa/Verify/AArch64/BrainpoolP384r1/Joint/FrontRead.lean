module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Points
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Math
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Loop
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Front

/-! Recover the public digit after the two complete doublings. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

theorem stepFront_ok {base : Addr} {P Q : Point C} {u v j : Nat} {s : State}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (h1 : 1 ≤ j) (h256 : j ≤ 192) (h : Running base P Q u v j s) :
    WP isa stepFront s fun t => Scr t base 8192 ∧
      t.gpr .x2=BitVec.ofNat 64 (digitPair u v (j-1)) := by
  rw [stepFront]
  refine WP.seq (WP.mono (decCounter_ok s h1 (by omega) h.counter) fun s₀ ⟨c₀,k₀⟩ => ?_)
  have W₀ : Changes base loopWork s s₀ := Changes.of_keeps k₀ (by decide)
  have I₀ := h.inputs.unch (W₀.mono loopWork_sub)
  have R₀ := h.point.of_mem k₀.mem
  have hA : onCurve C (stage P Q u v j)=true := pair_curve hC hP hQ _ _
  refine WP.seq (WP.mono (double_points hc hC I₀ hA R₀) fun s₁ ⟨k₁,I₁,R₁,c₁⟩ => ?_)
  refine WP.seq (WP.mono (double_points hc hC I₁ (hC.onCurve_add hA hA) R₁) fun s₂ ⟨k₂,I₂,_,c₂⟩ => ?_)
  have W₂ := (W₀.trans k₁).trans k₂
  have B₂ := (W₂.mono loopWork_sub).bits h.bits
  have C₂ : s₂.gpr .x19=BitVec.ofNat 64 (j-1) := c₂.trans (c₁.trans c₀)
  exact WP.mono (digit_ok I₂.scr B₂ (by omega) C₂) fun t ⟨d,k⟩ =>
    ⟨I₂.scr.of_keeps k (by decide),d⟩
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
