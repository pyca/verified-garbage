module

import VerifiedGarbage.Proof.Weierstrass.Arm.TCombMagnitude
public import VerifiedGarbage.Proof.Weierstrass.Arm.Bits
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombHorner

/-! Digit and sign decoding share the public window-address calculation. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Impl.Mont.Arm VG.Proof.X25519.Arm

theorem windowIndex_ok (K : TCombCfg) {s : State} {j : Nat}
    (hw : K.w<9) (gj : s.gpr .r11=BitVec.ofNat 32 j) :
    WP isa (.block K.windowIndex) s fun t =>
      t.gpr .r4=t.gpr .r12+BitVec.ofNat 32 (K.w*j+farOff K.L.bits) ∧ RegOnly [.r4] s t := by
  have enc : encodable (BitVec.ofNat 32 K.w)=true :=
    (by decide : ∀ w<9,encodable (BitVec.ofNat 32 w)=true) K.w hw
  unfold TCombCfg.windowIndex
  simp only [List.cons_append,List.nil_append]
  refine wp_mov (op2_imm enc) fun s₁ u₁ => wp_mul fun s₂ u₂ => wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  have k₁₂ : Rest [.r4] s s₂ := (u₁.rest (by simp)).trans (u₂.rest (by simp))
  have k₃ : Rest [.r4] s s₃ := k₁₂.trans (u₃.rest (by simp))
  have p : s₃.gpr .r4=s₃.gpr .r12+BitVec.ofNat 32 (K.w*j) := by
    rw [u₃.gpr,dpVal,u₂.gpr,u₁.gpr,u₁.other .r11 (by decide),gj,← BitVec.ofNat_mul,
      u₃.other .r12 (by decide)]
  rw [← List.append_nil (far .r4 K.L.bits)]
  refine wp_far (d := K.L.bits) p (by decide) fun s₄ k₄ m₄ p₄ => WP.block_nil
    ⟨p₄,⟨k₃.trans k₄,by rw [m₄,u₃.mem,u₂.mem,u₁.mem]⟩⟩

end VG.Proof.Weierstrass.Arm.TComb
