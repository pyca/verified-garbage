module

public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombLayout
public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombHorner
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombTail
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Reflect the selected affine point with the existing field subtraction and selection. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Point
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass.Arm.Point
open VG.Proof.X25519.Arm

theorem negate_ok (K : TCombCfg) {s : State} {base : Addr} {m : Nat} (positive : Prop)
    [Decidable positive] (h : Layout K) (hs : Scr s base 4096) (hf : Far s base 8192)
    (hm : K.F.m=m) (hn : K.F.k=K.L.M.n) (hM : Mont.ModOk K.L.M.n m)
    (hz : wordsVal s.mem base K.zero K.L.M.n=0)
    (hy : wordsVal s.mem base K.Q.y K.L.M.n<m)
    (hmask : ∀ u, Rest VG.Proof.Weierstrass.Arm.Mont.callClob s u →
      Unch base [(K.neg,8*K.L.M.n),(VG.Impl.Weierstrass.Arm.Mont.own K.L.M.n,64*K.L.M.n)] s.mem u.mem →
      WP isa K.signMask u fun v =>
        v.gpr .r10=(if positive then 0 else BitVec.allOnes 32) ∧ RegOnly [.r4,.r10] u v) :
    WP isa (.seq (VG.Impl.Weierstrass.Arm.Mont.subCall K.F K.neg K.zero K.Q.y)
      (.seq K.signMask (.block (sel (2*K.L.M.n) K.Q.y K.Q.y K.neg)))) s fun t =>
      Rest VG.Proof.Weierstrass.Arm.Mont.callClob s t ∧
      Unch base (loopWrites K) s.mem t.mem ∧
      (∀ x ∈ [K.L.R.x,K.L.R.y,K.L.R.z],
        wordsVal t.mem base x K.L.M.n=wordsVal s.mem base x K.L.M.n) ∧
      wordsVal t.mem base K.Q.x K.L.M.n=wordsVal s.mem base K.Q.x K.L.M.n ∧
      wordsVal t.mem base K.Q.y K.L.M.n=
        (if positive then wordsVal s.mem base K.Q.y K.L.M.n else
          (m-wordsVal s.mem base K.Q.y K.L.M.n)%m) ∧
      wordsVal t.mem base K.Q.z K.L.M.n=wordsVal s.mem base K.Q.z K.L.M.n := by
  have hl := lay_nums h.n3 h.n6
  have low := h.low
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] at low
  obtain ⟨rx,ry,rz,hzero,hneg⟩ := low
  have qfit : K.Q.y+8*K.L.M.n≤VG.Impl.Weierstrass.Arm.Mont.own K.L.M.n := by
    simp only [TCombCfg.Q,ptAt]
    exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide)
  have below : Impl.Weierstrass.Point.oAt K.L.M.n≤VG.Impl.Weierstrass.Arm.Mont.own K.L.M.n := by
    exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide)
  have fm : Mont.ModOk K.F.k K.F.m := by rw [hn,hm]; exact hM
  refine WP.seq (WP.mono (VG.Proof.Weierstrass.Arm.Mont.subCall_ok fm hs hf
    (by rw [hn]; omega) (by rw [hn]; omega) (by rw [hn]; exact qfit)
    (by rw [hn,hm,hz]; omega) (by rw [hn,hm]; exact hy)) fun u ⟨ku,yu⟩ => ?_)
  rw [hn,hm,hz,Nat.zero_add] at yu
  have ou := Outs.unch ku.mem
  rw [hn] at ou
  refine WP.seq (WP.mono (hmask u (by simpa only [hn] using ku.rest) ou)
    fun v ⟨mask,kv⟩ => ?_)
  have hsv := (hs.of_rest ku.rest (by decide)).of_rest kv.keep (by decide)
  have msk : v.gpr .r10=if decide (¬positive) then BitVec.allOnes 32 else 0 := by
    rw [mask]
    by_cases hp : positive <;> simp [hp]
  refine WP.mono (selField_ok hsv (decide (¬positive)) msk
    (o := K.Q.y) (a := K.Q.y) (b := K.neg) (n := K.L.M.n)
    (by simp only [TCombCfg.Q,ptAt]; omega) (by simp only [TCombCfg.Q,ptAt]; omega)
    (by omega) (.inl (Nat.le_refl _)) (.inr (by
      have b : Impl.Weierstrass.Point.oAt K.L.M.n≤K.Q.y := by
        simp only [TCombCfg.Q,ptAt]
        exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide)
      omega))) fun t ⟨yt,kt,ot⟩ => ?_
  have qold : ∀ x ∈ [K.Q.x,K.Q.y,K.Q.z],
      wordsVal v.mem base x K.L.M.n=wordsVal s.mem base x K.L.M.n := by
    intro x hx
    rw [kv.mem]
    apply ou.wordsVal
    · have geom : Impl.Weierstrass.Point.oAt K.L.M.n≤x ∧
          x+8*K.L.M.n≤VG.Impl.Weierstrass.Arm.Mont.own K.L.M.n := by
        simp only [TCombCfg.Q,ptAt] at hx
        exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide) x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
      exact ⟨.inr (by omega),.inl geom.2⟩
    · have geom : x+8*K.L.M.n≤4096 := by
        simp only [TCombCfg.Q,ptAt] at hx
        exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide) x hx
      omega
  refine ⟨ku.rest.trans ((kv.keep.mono (by simp [VG.Proof.Weierstrass.Arm.Mont.callClob,VG.Proof.Mont.Arm.clob])).trans
    (kt.mono (by simp [VG.Proof.Weierstrass.Arm.Mont.callClob,VG.Proof.Mont.Arm.clob]))),?_,?_,?_,?_,?_⟩
  · have ov : Unch base [(K.neg,8*K.L.M.n),(VG.Impl.Weierstrass.Arm.Mont.own K.L.M.n,64*K.L.M.n)] s.mem v.mem := by
      rw [kv.mem]; exact ou
    apply (ov.trans ot.unch).cover
    intro w hw
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with (rfl|rfl)|rfl
    · exact ⟨_,by simp [loopWrites],Nat.le_refl _,Nat.le_refl _⟩
    · refine ⟨(Impl.Weierstrass.Point.ownAt K.L.M.n,4096-Impl.Weierstrass.Point.ownAt K.L.M.n),by simp [loopWrites],?_⟩
      exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide)
    · refine ⟨(Impl.Weierstrass.Point.oAt K.L.M.n,72*K.L.M.n),by simp [loopWrites],?_⟩
      simp only [TCombCfg.Q,ptAt]
      exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide)
  · intro x hx
    have lowx := h.low x (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; rcases hx with rfl|rfl|rfl <;> simp)
    have negx := h.negApart x (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; rcases hx with rfl|rfl|rfl <;> simp)
    have qy : Impl.Weierstrass.Point.oAt K.L.M.n≤K.Q.y := by
      simp only [TCombCfg.Q,ptAt]
      exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide)
    rw [ot.wordsVal (.inl (Nat.le_trans lowx qy)) (by omega),kv.mem]
    apply ou.wordsVal
    · simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
      exact ⟨negx.symm,.inl (Nat.le_trans lowx below)⟩
    · omega
  · rw [ot.wordsVal (by simp only [TCombCfg.Q,ptAt,Impl.Weierstrass.Point.elemBytes]; omega)
      (by simp only [TCombCfg.Q,ptAt,Impl.Weierstrass.Point.elemBytes]; omega),qold _ (by simp)]
  · rw [yt,kv.mem,yu]
    have qo := qold K.Q.y (by simp)
    rw [kv.mem] at qo
    rw [qo]
    by_cases hp : positive <;> simp [hp]
  · rw [ot.wordsVal (by simp only [TCombCfg.Q,ptAt,Impl.Weierstrass.Point.elemBytes]; omega)
      (by simp only [TCombCfg.Q,ptAt,Impl.Weierstrass.Point.elemBytes]; omega),qold _ (by simp)]

end VG.Proof.Weierstrass.Arm.TComb
