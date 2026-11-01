module

import VerifiedGarbage.Proof.Weierstrass.Arm.TCombBody
import VerifiedGarbage.Proof.Weierstrass.Arm.Const
import VerifiedGarbage.Proof.Weierstrass.Arm.Copy
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.Arm.Words
public import VerifiedGarbage.Impl.Weierstrass.Arm
public import VerifiedGarbage.Impl.Weierstrass.Arm.TComb
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombMask

/-! Complete the selected affine point, including the zero digit's infinity. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Impl.Mont.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.X25519.Arm

theorem selField_ok {s : State} {base : Addr} {size n o a b : Nat} (hs : Scr s base size)
    (c : Bool) (hc : s.gpr .r10=if c then BitVec.allOnes 32 else 0)
    (ho : o+8*n≤size) (ha : a+8*n≤size) (hb : b+8*n≤size)
    (hoa : o≤a ∨ a+8*n≤o) (hob : o≤b ∨ b+8*n≤o) :
    WP isa (.block (sel (2*n) o a b)) s fun t =>
      wordsVal t.mem base o n=(if c then wordsVal s.mem base b n else wordsVal s.mem base a n) ∧
      Rest [.r4,.r5] s t ∧ Outside base o (8*n) s.mem t.mem := by
  simp only [wordsVal_eq_val32]
  simpa only [show 4*(2*n)=8*n by omega] using
    (sel_ok c (2*n) hs hc (by omega) (by omega) (by omega) (by omega) (by omega))

theorem selectTail_ok (K : TCombCfg) {s : State} {base : Addr} {size a : Nat}
    (hs : Scr s base size) (hq : K.Q.x+24*K.L.M.n≤size)
    (hzle : K.zero+8*K.L.M.n≤size)
    (hza : K.zero+8*K.L.M.n≤K.Q.x ∨ K.Q.x+24*K.L.M.n≤K.zero)
    (hone : K.one<2^(64*K.L.M.n))
    (ha : a<2^31) (ga : s.gpr .r9=BitVec.ofNat 32 a)
    (hz : wordsVal s.mem base K.zero K.L.M.n=0) :
    WP isa (.block K.selectTail) s fun t =>
      wordsVal t.mem base K.Q.x K.L.M.n=wordsVal s.mem base K.Q.x K.L.M.n ∧
      wordsVal t.mem base K.Q.y K.L.M.n=(if a=0 then K.one else wordsVal s.mem base K.Q.y K.L.M.n) ∧
      wordsVal t.mem base K.Q.z K.L.M.n=(if a=0 then 0 else K.one) ∧
      Rest [.r4,.r5,.r10] s t ∧ Outside base K.Q.x (24*K.L.M.n) s.mem t.mem := by
  have hy : K.Q.y=K.Q.x+8*K.L.M.n := rfl
  have hzz : K.Q.z=K.Q.x+16*K.L.M.n := by
    simp only [TCombCfg.Q, VG.Impl.Weierstrass.Arm.Point.ptAt, Impl.Weierstrass.Point.elemBytes]
    omega
  have hn := hs.nowrap
  unfold TCombCfg.selectTail
  rw [List.append_assoc,List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (setConst_ok hs (o := K.Q.z) (n := K.L.M.n)
    (by rw [hzz]; omega) hone) fun s₁ ⟨one₁,k₁,O₁⟩ => ?_
  refine VG.Proof.X25519.Arm.WP.append (eqMask_ok (op2_imm (by decide))) fun s₂ ⟨mask₂,k₂,mem₂⟩ => ?_
  have k₁₂ : Rest [.r4,.r5,.r10] s s₂ := (k₁.mono (by simp)).trans (k₂.mono (by simp))
  have hs₂ := hs.of_rest k₁₂ (by decide)
  have cm₂ : s₂.gpr .r10=if decide (a=0) then BitVec.allOnes 32 else 0 := by
    rw [mask₂,k₁.gpr .r9 (by decide),ga]
    change 0#32-(((BitVec.ofNat 32 a ^^^ 0#32)-1) >>> 31)=_
    rw [equality_mask (by simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show a<2^32 by omega)]; exact ha)
      (by decide)]
    have e : BitVec.ofNat 32 a=0#32 ↔ a=0 := by
      exact ofNat32_eq (by omega) (by decide)
    simp only [e,decide_eq_true_eq]
  refine VG.Proof.X25519.Arm.WP.append (selField_ok hs₂ (decide (a=0)) cm₂
    (o := K.Q.y) (a := K.Q.y) (b := K.Q.z) (n := K.L.M.n)
    (by rw [hy]; omega) (by rw [hy]; omega) (by rw [hzz]; omega)
    (.inl (Nat.le_refl _)) (.inl (by rw [hy,hzz]; omega))) fun s₃ ⟨y₃,k₃,O₃⟩ => ?_
  have k₁₃ : Rest [.r4,.r5,.r10] s s₃ := k₁₂.trans (k₃.mono (by simp))
  have hs₃ := hs.of_rest k₁₃ (by decide)
  have cm₃ : s₃.gpr .r10=if decide (a=0) then BitVec.allOnes 32 else 0 := by
    rw [k₃.gpr .r10 (by decide),cm₂]
  refine WP.mono (selField_ok hs₃ (decide (a=0)) cm₃
    (o := K.Q.z) (a := K.Q.z) (b := K.zero) (n := K.L.M.n)
    (by rw [hzz]; omega) (by rw [hzz]; omega) hzle (.inl (Nat.le_refl _)) (by rw [hzz]; omega))
    fun s₄ ⟨z₄,k₄,O₄⟩ => ?_
  have oldx : wordsVal s₄.mem base K.Q.x K.L.M.n=wordsVal s.mem base K.Q.x K.L.M.n := by
    rw [O₄.wordsVal (by rw [hzz]; omega) (by omega),O₃.wordsVal (by rw [hy]; omega) (by omega),
      mem₂,O₁.wordsVal (by rw [hzz]; omega) (by omega)]
  have oldy : wordsVal s₂.mem base K.Q.y K.L.M.n=wordsVal s.mem base K.Q.y K.L.M.n := by
    rw [mem₂,O₁.wordsVal (by rw [hy,hzz]; omega) (by omega)]
  have oz : wordsVal s₃.mem base K.Q.z K.L.M.n=K.one := by
    rw [O₃.wordsVal (by rw [hy,hzz]; omega) (by omega),mem₂,one₁]
  have zero₃ : wordsVal s₃.mem base K.zero K.L.M.n=0 := by
    rw [O₃.wordsVal (by rw [hy]; omega) (by omega),mem₂,
      O₁.wordsVal (by rw [hzz]; omega) (by omega),hz]
  refine ⟨oldx,?_,?_,k₁₃.trans (k₄.mono (by simp)),?_⟩
  · rw [O₄.wordsVal (by rw [hy,hzz]; omega) (by omega),y₃,mem₂,one₁]
    simp only [decide_eq_true_eq]
    split <;> first | rfl | exact mem₂ ▸ oldy
  · rw [z₄,oz,zero₃]
    simp only [decide_eq_true_eq]
  · have O₂ : Outside base K.Q.x (24*K.L.M.n) s₁.mem s₂.mem := by rw [mem₂]; exact Outside.refl _ _ _ _
    exact ((O₁.mono (by rw [hzz]; omega) (by rw [hzz]; omega)).trans O₂).trans
      ((O₃.mono (by rw [hy]; omega) (by rw [hy]; omega)).trans
        (O₄.mono (by rw [hzz]; omega) (by rw [hzz]; omega)))

end VG.Proof.Weierstrass.Arm.TComb
