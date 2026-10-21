module

import VerifiedGarbage.Proof.Weierstrass.Arm.TCombLoop
import VerifiedGarbage.Proof.Weierstrass.Arm.Const
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.Arm.Words
public import VerifiedGarbage.Impl.Weierstrass.Arm.TComb

/-! Initialize the same read-only comb table layout used by P-256. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Impl.Mont.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.X25519.Arm

theorem selectSetup_ok (K : TCombCfg) {s : State} {base : Addr} {size j : Nat}
    (hs : Scr s base size) (ho : K.Q.x+16*K.L.M.n ≤ size)
    (gj : s.gpr .r11=BitVec.ofNat 32 j)
    (enc : encodable (BitVec.ofNat 32 (16*K.L.M.n*K.H))=true) :
    WP isa (.block K.selectSetup) s fun t =>
      t.gpr .r8=s.syms K.tsym+BitVec.ofNat 32 (16*K.L.M.n*K.H*j) ∧
      t.gpr .r7=1 ∧ (∀ i<4*K.L.M.n,w32 t.mem base (K.Q.x+4*i)=0) ∧
      Rest [.r4,.r7,.r8] s t ∧ Outside base K.Q.x (16*K.L.M.n) s.mem t.mem := by
  have hy : K.Q.y=K.Q.x+8*K.L.M.n := rfl
  have hn := hs.nowrap
  unfold TCombCfg.selectSetup
  simp only [List.cons_append]
  refine WP.cons (s' := s.setReg .r8 (s.syms K.tsym)) rfl ?_
  let s₁ := s.setReg .r8 (s.syms K.tsym)
  have u₁ : Upd s s₁ .r8 (s.syms K.tsym) := Upd.setReg _ _ _
  refine wp_mov (op2_imm enc) fun s₂ u₂ => wp_mul fun s₃ u₃ =>
    wp_dp (op2_reg _ _) fun s₄ u₄ => ?_
  have k₁₂ : Rest [.r4,.r8] s s₂ := (u₁.rest (by simp)).trans (u₂.rest (by simp))
  have k₃₄ : Rest [.r4,.r8] s₂ s₄ := (u₃.rest (by simp)).trans (u₄.rest (by simp))
  have k₄ := k₁₂.trans k₃₄
  have hs₄ := hs.of_rest k₄ (by decide)
  have mem₄ : s₄.mem=s.mem := by rw [u₄.mem,u₃.mem,u₂.mem,u₁.mem]
  have g₈ : s₄.gpr .r8=s.syms K.tsym+BitVec.ofNat 32 (16*K.L.M.n*K.H*j) := by
    rw [u₄.gpr,dpVal,u₃.other .r8 (by decide),u₂.other .r8 (by decide),u₁.gpr,
      u₃.gpr,u₂.gpr,u₂.other .r11 (by decide),u₁.other .r11 (by decide),gj,← BitVec.ofNat_mul]
  rw [List.append_assoc,setConst_eq]
  refine VG.Proof.X25519.Arm.WP.append
    (constSteps_ok hs₄ (o := K.Q.x) (x := 0) (2*K.L.M.n) (by omega))
    fun s₅ ⟨vx,k₅,Ox⟩ => ?_
  have hs₅ := hs₄.of_rest k₅ (by decide)
  rw [setConst_eq]
  refine VG.Proof.X25519.Arm.WP.append
    (constSteps_ok hs₅ (o := K.Q.y) (x := 0) (2*K.L.M.n) (by rw [hy]; omega))
    fun s₆ ⟨vy,k₆,Oy⟩ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₇ u₇ => WP.block_nil ?_
  have mem₇ : s₇.mem=s₆.mem := u₇.mem
  have k₄₇ : Rest [.r4,.r7] s₄ s₇ := (k₅.mono (by simp)).trans
    ((k₆.mono (by simp)).trans (u₇.rest (by simp)))
  refine ⟨?_,u₇.gpr,?_,(k₄.mono (by simp)).trans (k₄₇.mono (by simp)),?_⟩
  · rw [k₄₇.gpr .r8 (by decide),g₈]
  · intro i hi
    rw [mem₇]
    by_cases hx : i<2*K.L.M.n
    · rw [Oy.w32 (by rw [hy]; omega) (by omega),vx i hx]
      simp only [Nat.zero_shiftRight,Nat.zero_mod]
    · have hyi : i-2*K.L.M.n<2*K.L.M.n := by omega
      rw [show K.Q.x+4*i=K.Q.y+4*(i-2*K.L.M.n) by rw [hy]; omega,vy _ hyi]
      simp only [Nat.zero_shiftRight,Nat.zero_mod]
  · rw [mem₇,← mem₄]
    exact (Ox.mono (Nat.le_refl _) (by omega)).trans (Oy.mono (by rw [hy]; omega) (by rw [hy]; omega))

end VG.Proof.Weierstrass.Arm.TComb
