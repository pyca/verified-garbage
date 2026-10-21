module

import VerifiedGarbage.Proof.Weierstrass.Arm.TCombScan
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Impl.Weierstrass.Arm.TComb
public import VerifiedGarbage.Proof.Mont.Arm.Words
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombMask

/-! One public-index iteration of the signed comb table scan. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Impl.Mont.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.X25519.Arm

theorem ofNat32_eq {a b : Nat} (ha : a<2^32) (hb : b<2^32) :
    BitVec.ofNat 32 a = BitVec.ofNat 32 b ↔ a=b := by
  constructor
  · intro h
    have e := congrArg BitVec.toNat h
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using e
  · intro h; rw [h]

theorem sub_zero_iff (x y : BitVec 32) : x-y=0#32 ↔ x=y := by
  constructor
  · intro h
    have e := congrArg (fun z : BitVec 32 => z+y) h
    simpa only [BitVec.sub_add_cancel,BitVec.zero_add] using e
  · intro h; rw [h,BitVec.sub_self]

theorem selectBody_ok (K : TCombCfg) {s : State} {base X : Addr} {size a m : Nat}
    (hs : Scr s base size) (hX : State.addr (s.gpr .r8)=X)
    (ho : K.Q.x+16*K.L.M.n ≤ size) (hi : 16*K.L.M.n ≤ 4096)
    (fit : X.toNat+16*K.L.M.n ≤ 2^32)
    (hr : InRegions (s.rd ++ s.wr) X (16*K.L.M.n))
    (hd : Region.Disjoint ⟨X,16*K.L.M.n⟩ ⟨base,size⟩)
    (ha : a<2^31) (hm : m<2^31)
    (ga : s.gpr .r9=BitVec.ofNat 32 a) (gm : s.gpr .r7=BitVec.ofNat 32 m)
    (es : encodable (BitVec.ofNat 32 (16*K.L.M.n))=true)
    (eh : encodable (BitVec.ofNat 32 (K.H+1))=true)
    (mh : m+1<2^32) (hh : K.H+1<2^32) :
    WP isa (.block K.selectBody) s fun t =>
      (∀ i<4*K.L.M.n, w32 t.mem base (K.Q.x+4*i) =
        if a=m then w32 s.mem X (4*i) else w32 s.mem base (K.Q.x+4*i)) ∧
      Rest [.r4,.r5,.r7,.r8,.r10] s t ∧ Outside base K.Q.x (16*K.L.M.n) s.mem t.mem ∧
      t.gpr .r8=s.gpr .r8+BitVec.ofNat 32 (16*K.L.M.n) ∧
      t.gpr .r7=BitVec.ofNat 32 (m+1) ∧ t.z=decide (m+1=K.H+1) := by
  unfold TCombCfg.selectBody
  rw [List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (eqMask_ok (op2_reg s .r7)) fun s₁ ⟨v₁,k₁,mem₁⟩ => ?_
  have cm₁ : s₁.gpr .r10=if decide (a=m) then BitVec.allOnes 32 else 0 := by
    rw [v₁,ga,gm,equality_mask (by simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show a<2^32 by omega)] using ha)
      (by simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show m<2^32 by omega)] using hm)]
    simp only [ofNat32_eq (by omega : a<2^32) (by omega : m<2^32),decide_eq_true_eq]
  have hs₁ := hs.of_rest k₁ (by decide)
  have hx₁ : State.addr (s₁.gpr .r8)=X := by rw [k₁.gpr .r8 (by decide),hX]
  have hr₁ : InRegions (s₁.rd ++ s₁.wr) X (16*K.L.M.n) := by rw [k₁.rd,k₁.wr]; exact hr
  refine VG.Proof.X25519.Arm.WP.append
    (selectWords_ok K hs₁ hx₁ ho hi fit hr₁ hd (decide (a=m)) cm₁ (4*K.L.M.n) (Nat.le_refl _))
    fun s₂ ⟨v₂,k₂,O₂⟩ => ?_
  have k₁₂ : Rest [.r4,.r5,.r10] s s₂ := (k₁.mono (by simp)).trans (k₂.mono (by simp))
  refine wp_dp (op2_imm es) fun s₃ u₃ => wp_dp (op2_imm (by decide)) fun s₄ u₄ =>
    wp_cmp (op2_imm eh) fun s₅ f₅ z₅ => WP.block_nil ?_
  have k₃₅ : Rest [.r7,.r8] s₂ s₅ := (u₃.rest (by simp)).trans
    ((u₄.rest (by simp)).trans (f₅.rest _))
  have mem₅ : s₅.mem=s₂.mem := by rw [f₅.mem,u₄.mem,u₃.mem]
  have g₇ : s₅.gpr .r7=BitVec.ofNat 32 (m+1) := by
    rw [f₅.gpr,u₄.gpr,dpVal,u₃.other .r7 (by decide),k₁₂.gpr .r7 (by decide),gm]
    exact (BitVec.ofNat_add _ _).symm
  refine ⟨?_, (k₁₂.mono (by simp)).trans (k₃₅.mono (by simp)),?_,?_,g₇,?_⟩
  · intro i hii
    rw [mem₅,v₂ i hii,mem₁]
    simp only [decide_eq_true_eq]
  · rw [mem₁] at O₂
    rw [mem₅]
    simpa only [show 4*(4*K.L.M.n)=16*K.L.M.n by omega] using O₂
  · rw [f₅.gpr,u₄.other .r8 (by decide),u₃.gpr,dpVal,k₁₂.gpr .r8 (by decide)]
  · have g₇' : s₄.gpr .r7=BitVec.ofNat 32 (m+1) := by rw [← f₅.gpr,g₇]
    rw [z₅,g₇']
    have e : (BitVec.ofNat 32 (m+1)-BitVec.ofNat 32 (K.H+1)==0) = decide (m+1=K.H+1) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq,decide_eq_true_eq]
      change BitVec.ofNat 32 (m+1)-BitVec.ofNat 32 (K.H+1)=0#32 ↔ m+1=K.H+1
      rw [sub_zero_iff,ofNat32_eq mh hh]
    exact e

end VG.Proof.Weierstrass.Arm.TComb
