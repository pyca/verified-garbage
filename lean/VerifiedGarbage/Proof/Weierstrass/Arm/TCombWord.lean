module

import VerifiedGarbage.Proof.Weierstrass.Arm.TCombMask
public import VerifiedGarbage.Proof.Mont.Arm.Words
import VerifiedGarbage.Proof.Mont.Arm.Csub
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Weierstrass.Arm.TComb
public import VerifiedGarbage.Proof.X25519.Arm.Instr

/-! One word of the fixed-base comb's constant-time table scan. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Impl.Mont.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.X25519.Arm

theorem selectWord_ok (K : TCombCfg) {s : State} {base X : Addr} {size i : Nat}
    (hs : Scr s base size) (hX : State.addr (s.gpr .r8) = X)
    (ho : K.Q.x+4*i+4 ≤ size) (hi : 4*i+4 ≤ 4096)
    (fit : X.toNat+4*i+4 ≤ 2^32)
    (hr : InRegions (s.rd ++ s.wr) (off X (4*i)) 4)
    (b : Bool) (hc : s.gpr .r10 = if b then BitVec.allOnes 32 else 0) :
    WP isa (.block (K.selectWord i)) s fun t =>
      t.mem.readW (off base (K.Q.x+4*i)) 32 =
        (if b then s.mem.readW (off X (4*i)) 32 else s.mem.readW (off base (K.Q.x+4*i)) 32) ∧
      Rest [.r4,.r5] s t ∧ Outside base (K.Q.x+4*i) 4 s.mem t.mem := by
  have hn := hs.nowrap
  have hxnat : (s.gpr .r8).toNat = X.toNat := by
    rw [← hX,addr_toNat]
  have hea : State.addr (s.gpr .r8+BitVec.ofNat 32 (4*i)) = off X (4*i) := by
    rw [VG.Arm.addr_add (by omega_using [fit,hxnat]),hX]
  unfold TCombCfg.selectWord
  refine wp_ldr (hs.off_lt (by omega_using [ho])) (hs.ea (by omega_using [ho])) (hs.read ho)
    fun s₁ u₁ => ?_
  have hs₁ := hs.of_rest (u₁.rest (ws := [.r4]) (by simp)) (by decide)
  have ea₁ : State.addr (s₁.gpr .r8+BitVec.ofNat 32 (4*i)) = off X (4*i) := by
    rw [u₁.other .r8 (by decide),hea]
  have hr₁ : InRegions (s₁.rd ++ s₁.wr) (off X (4*i)) 4 := by rw [u₁.rd,u₁.wr]; exact hr
  refine wp_ldr (by omega_using [hi]) ea₁ hr₁ fun s₂ u₂ =>
    wp_dp (op2_reg _ _) fun s₃ u₃ => wp_dp (op2_reg _ _) fun s₄ u₄ =>
    wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  have k₅ : Rest [.r4,.r5] s s₅ := (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans
    ((u₃.rest (by simp)).trans ((u₄.rest (by simp)).trans (u₅.rest (by simp)))))
  have hs₅ := hs.of_rest k₅ (by decide)
  refine wp_str (hs.off_lt (by omega_using [ho])) (hs₅.ea (by omega_using [ho])) (hs₅.write ho)
    fun s₆ m₆ => WP.block_nil ?_
  have a₂ : s₂.gpr .r4 = s.mem.readW (off base (K.Q.x+4*i)) 32 := by
    rw [u₂.other .r4 (by decide),u₁.gpr]
  have d₂ : s₂.gpr .r5 = s.mem.readW (off X (4*i)) 32 := by rw [u₂.gpr,u₁.mem]
  have c₂ : s₂.gpr .r10 = s.gpr .r10 := by
    rw [u₂.other .r10 (by decide),u₁.other .r10 (by decide)]
  have d₃ : s₃.gpr .r5 = s.mem.readW (off X (4*i)) 32 ^^^ s.mem.readW (off base (K.Q.x+4*i)) 32 := by
    rw [u₃.gpr,dpVal,d₂,a₂]
  have d₄ : s₄.gpr .r5 = (s.mem.readW (off X (4*i)) 32 ^^^ s.mem.readW (off base (K.Q.x+4*i)) 32) &&&
      (if b then BitVec.allOnes 32 else 0) := by
    rw [u₄.gpr,dpVal,d₃,u₃.other .r10 (by decide),c₂,hc]
  have v₅ : s₅.gpr .r4 = if b then s.mem.readW (off X (4*i)) 32 else s.mem.readW (off base (K.Q.x+4*i)) 32 := by
    rw [u₅.gpr,dpVal,d₄,u₄.other .r4 (by decide),u₃.other .r4 (by decide),a₂]
    exact select_val _ _ b
  have mem₅ : s₅.mem=s.mem := by rw [u₅.mem,u₄.mem,u₃.mem,u₂.mem,u₁.mem]
  refine ⟨?_,k₅.trans (m₆.rest _),?_⟩
  · rw [m₆.mem,Mem.readW_writeW_self32,v₅]
  · rw [m₆.mem,mem₅]; exact writeW32_outside _ _ _ (by omega_using [ho,hn])

end VG.Proof.Weierstrass.Arm.TComb
