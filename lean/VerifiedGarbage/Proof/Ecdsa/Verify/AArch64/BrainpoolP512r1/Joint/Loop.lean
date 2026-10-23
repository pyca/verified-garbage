module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.LoopOps
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.Math
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.Table

/-! One shared Horner loop advances both public verification scalars. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint

structure Running (base : Addr) (P Q : Point C) (u v j : Nat) (s : State) : Prop where
  inputs : Inputs base P Q s
  bits : Bits base u v s
  table : Table base P Q 15 s
  counter : s.gpr .x19 = BitVec.ofNat 64 j
  point : PointAt base s resultPt (stage P Q u v j)

theorem step_ok {base : Addr} {P Q : Point C} {u v j : Nat} {s : State}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (h1 : 1 ≤ j) (h256 : j ≤ 256) (h : Running base P Q u v j s) :
    WP isa step s fun t => Changes base loopWork s t ∧ Running base P Q u v (j-1) t := by
  rw [step]
  refine WP.seq (WP.mono (decCounter_ok s h1 (by omega) h.counter) fun s₀ ⟨c₀,k₀⟩ => ?_)
  have W₀ : Changes base loopWork s s₀ := Changes.of_keeps k₀ (by decide)
  have I₀ := h.inputs.unch (W₀.mono loopWork_sub)
  have R₀ := h.point.of_mem k₀.mem
  have hA : onCurve C (stage P Q u v j)=true := pair_curve hC hP hQ _ _
  refine WP.seq (WP.mono (double_points hc hC I₀ hA R₀) fun s₁ ⟨k₁,I₁,R₁,c₁⟩ => ?_)
  refine WP.seq (WP.mono (double_points hc hC I₁ (hC.onCurve_add hA hA) R₁) fun s₂ ⟨k₂,I₂,R₂,c₂⟩ => ?_)
  have W₂ := (W₀.trans k₁).trans k₂
  have B₂ := (W₂.mono loopWork_sub).bits h.bits
  have T₂ := h.table.of_changes h.inputs.scr W₂
  have C₂ : s₂.gpr .x19=BitVec.ofNat 64 (j-1) := c₂.trans (c₁.trans c₀)
  have hAA := hC.onCurve_add hA hA
  refine WP.mono (addDigit_ok hc hC hP hQ (hC.onCurve_add hAA hAA) I₂ B₂ T₂ R₂
    (by omega) C₂) fun t ⟨k₃,I₃,B₃,T₃,R₃,c₃⟩ => ?_
  have eqj : j-1+1=j := by omega
  have em := at_step hC hP hQ u v (j-1)
  rw [eqj] at em
  have hcmt := point_comm hC
    (pair_curve hC hP hQ ((u >>> (2*(j-1)))%4) ((v >>> (2*(j-1)))%4))
    (hC.onCurve_add hAA hAA)
  have final : add (pair P Q ((u >>> (2*(j-1)))%4) ((v >>> (2*(j-1)))%4))
      (add (add (stage P Q u v j) (stage P Q u v j))
        (add (stage P Q u v j) (stage P Q u v j))) = stage P Q u v (j-1) := hcmt.trans em
  rw [final] at R₃
  exact ⟨W₂.trans k₃,⟨I₃,B₃,T₃,c₃.trans C₂,R₃⟩⟩

theorem loop_ok {base : Addr} {P Q : Point C} {u v : Nat} {s : State}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (h : Running base P Q u v 256 s) :
    WP isa (.loop step (.nonzero .x .x19)) s fun t =>
      Changes base loopWork s t ∧ Running base P Q u v 0 t := by
  let inv := fun j t => Changes base loopWork s t ∧ Running base P Q u v j t
  refine countLoop_ok (Inv:=inv) (n:=256) (by decide) (fun j t h1 h256 ⟨k,hi⟩ => ?_)
    (fun _ h => h) (by decide) ⟨⟨rfl,rfl,rfl,rfl,Unch.refl _ _ _⟩,h⟩
  exact WP.mono (step_ok hc hC hP hQ h1 h256 hi) fun u ⟨k',hi'⟩ => ⟨⟨k.trans k',hi'⟩,hi'.counter⟩
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint
