module

public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombHorner
import VerifiedGarbage.Proof.Framework.Block

/-! The signed digit's magnitude uses the same arithmetic theorem as x86. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Proof.X25519.Arm

theorem magnitude_ok (K : TCombCfg) {s : State} {v : Nat}
    (hw : K.w<9) (hv : v<2^K.w) (gv : s.gpr .r9=BitVec.ofNat 32 v) :
    WP isa (.block K.magnitude) s fun t =>
      t.gpr .r9=BitVec.ofNat 32 (magH K.H v) ∧ RegOnly [.r4,.r5,.r9] s t := by
  have enc : encodable (BitVec.ofNat 32 K.H)=true :=
    (by decide : ∀ w<9,encodable (BitVec.ofNat 32 (2^(w-1)))=true) K.w hw
  unfold TCombCfg.magnitude
  refine wp_dp (op2_imm enc) fun s₁ u₁ => wp_mov (op2_lsr (by decide)) fun s₂ u₂ =>
    wp_mov (op2_imm (by decide)) fun s₃ u₃ => wp_dp (op2_reg _ _) fun s₄ u₄ =>
    wp_dp (op2_reg _ _) fun s₅ u₅ => wp_dp (op2_reg _ _) fun s₆ u₆ => WP.block_nil ?_
  let D := BitVec.ofNat 32 v-BitVec.ofNat 32 K.H
  let M := 0#32-(D >>> 31)
  have hd : s₁.gpr .r9=D := by rw [u₁.gpr,dpVal,gv]
  have hs : s₂.gpr .r4=D >>> 31 := by rw [u₂.gpr,hd]
  have hm : s₄.gpr .r4=M := by
    rw [u₄.gpr,dpVal,u₃.gpr,u₃.other .r4 (by decide),hs]; rfl
  have hn : s₅.gpr .r9=D ^^^ M := by
    rw [u₅.gpr,dpVal,hm,u₄.other .r9 (by decide),u₃.other .r9 (by decide),u₂.other .r9 (by decide),hd]
  have k₁₂ : Rest [.r4,.r5,.r9] s s₂ := (u₁.rest (by simp)).trans (u₂.rest (by simp))
  have k₃₄ : Rest [.r4,.r5,.r9] s₂ s₄ := (u₃.rest (by simp)).trans (u₄.rest (by simp))
  have k₅₆ : Rest [.r4,.r5,.r9] s₄ s₆ := (u₅.rest (by simp)).trans (u₆.rest (by simp))
  refine ⟨?_,⟨(k₁₂.trans k₃₄).trans k₅₆,by rw [u₆.mem,u₅.mem,u₄.mem,u₃.mem,u₂.mem,u₁.mem]⟩⟩
  rw [u₆.gpr,dpVal,hn,u₅.other .r4 (by decide),hm]
  exact magH_fact K.w hw v hv

end VG.Proof.Weierstrass.Arm.TComb
