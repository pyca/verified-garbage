module

public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombLayout
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Copy an accumulator into the existing point-add routine and copy its result back. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Point
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass.Arm.Point
open VG.Proof.X25519.Arm

/-- Reuse the point-call implementation for the comb's single addition per digit. -/
theorem add_ok (K : TCombCfg) {s : State} {base : Addr} {m : Nat} [NeZero m]
    (h : Layout K) (hs : Scr s base 4096) (hf : Far s base 8192)
    (hm : K.F.m=m) (hn : K.F.k=K.L.M.n) (hM : Mont.ModOk K.L.M.n m)
    (hlt : ∀ x ∈ [K.L.R.x,K.L.R.y,K.L.R.z,K.Q.x,K.Q.y,K.Q.z,
      Impl.Weierstrass.Point.aAt K.L.M.n,Impl.Weierstrass.Point.b3At K.L.M.n],
      wordsVal s.mem base x K.L.M.n<m) :
    WP isa K.add s fun t =>
      Rest [.r4,.r10,.r0,.r1,.r2,.r3] s t ∧ Unch base (loopWrites K) s.mem t.mem ∧
      (∀ x ∈ [K.L.R.x,K.L.R.y,K.L.R.z], wordsVal t.mem base x K.L.M.n<m) ∧
      (toM m (2^(64*K.L.M.n)) (wordsVal t.mem base K.L.R.x K.L.M.n),
       toM m (2^(64*K.L.M.n)) (wordsVal t.mem base K.L.R.y K.L.M.n),
       toM m (2^(64*K.L.M.n)) (wordsVal t.mem base K.L.R.z K.L.M.n))=
        rcbAdd (Eb K.L.M.n m false s.mem base 9) (Eb K.L.M.n m false s.mem base 10)
          (toM m (2^(64*K.L.M.n)) (wordsVal s.mem base K.L.R.x K.L.M.n))
          (toM m (2^(64*K.L.M.n)) (wordsVal s.mem base K.L.R.y K.L.M.n))
          (toM m (2^(64*K.L.M.n)) (wordsVal s.mem base K.L.R.z K.L.M.n))
          (Eb K.L.M.n m false s.mem base 6) (Eb K.L.M.n m false s.mem base 7)
          (Eb K.L.M.n m false s.mem base 8) := by
  unfold TCombCfg.add
  have hl := lay_nums h.n3 h.n6
  have low := h.low
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] at low hlt
  obtain ⟨rx,ry,rz,hzero,hneg⟩ := low
  obtain ⟨lx,ly,lz,lqx,lqy,lqz,la,lb⟩ := hlt
  have cp := copyPt_conds (a := K.L.R) h.n3 h.n6 rfl (.inl rfl)
    (Nat.le_trans rx (oAt_le_pAt _)) (Nat.le_trans ry (oAt_le_pAt _)) (Nat.le_trans rz (oAt_le_pAt _))
  refine WP.seq (WP.mono (copyPt_ok hs cp.1 cp.2.1 cp.2.2) fun u ⟨px,py,pz,keep,outs⟩ => ?_)
  simp only [TCombCfg.P,ptAt] at px py pz outs
  have hsu := hs.of_rest keep (by decide)
  have hfu := hf.of_rest keep
  have other : ∀ x ∈ [K.Q.x,K.Q.y,K.Q.z,Impl.Weierstrass.Point.aAt K.L.M.n,
      Impl.Weierstrass.Point.b3At K.L.M.n],
      wordsVal u.mem base x K.L.M.n=wordsVal s.mem base x K.L.M.n := by
    intro x hx
    apply (Outs.unch outs).wordsVal
    · simp only [TCombCfg.Q,ptAt] at hx
      exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide) x hx
    · have := hs.nowrap
      have bx : x+8*K.L.M.n≤4096 := by
        simp only [TCombCfg.Q,ptAt] at hx
        exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide) x hx
      omega_arith
  have hltu : ∀ x ∈ rIds,wordsVal u.mem base (enc K.L.M.n false x) K.L.M.n<m := by
    apply rIds_lt_of false
    simp only [Bool.false_eq_true,↓reduceIte,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [px]; exact lx
    · rw [py]; exact ly
    · rw [pz]; exact lz
    · change wordsVal u.mem base K.Q.x K.L.M.n<m
      rw [other K.Q.x (by simp)]; exact lqx
    · change wordsVal u.mem base K.Q.y K.L.M.n<m
      rw [other K.Q.y (by simp)]; exact lqy
    · change wordsVal u.mem base K.Q.z K.L.M.n<m
      rw [other K.Q.z (by simp)]; exact lqz
    · rw [other _ (by simp)]; exact la
    · rw [other _ (by simp)]; exact lb
  refine WP.seq (WP.mono (ptCall_ok hm hn hM (ModOk.odd hM) h.n6 false hsu hfu hltu)
    fun v ⟨kv,ov,lv,eqv⟩ => ?_)
  have hsv := hsu.of_rest kv (by decide)
  have backIn : ∀ d ∈ [K.L.R.x,K.L.R.y,K.L.R.z,K.O.x,K.O.y,K.O.z],d+8*K.L.M.n≤4096 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    refine ⟨by omega_arith,by omega_arith,by omega_arith,?_⟩
    simp only [TCombCfg.O,ptAt]
    exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide)
  have backApart : ∀ d ∈ [K.L.R.x,K.L.R.y,K.L.R.z],∀ e ∈ [K.O.x,K.O.y,K.O.z],
      d+8*K.L.M.n≤e ∨ e+8*K.L.M.n≤d := by
    intro d hd e he
    have dl : d+8*K.L.M.n≤Impl.Weierstrass.Point.oAt K.L.M.n := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
      rcases hd with rfl|rfl|rfl <;> with_reducible assumption
    have el : Impl.Weierstrass.Point.oAt K.L.M.n≤e := by
      simp only [TCombCfg.O,ptAt] at he
      exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide) e he
    exact .inl (Nat.le_trans dl el)
  refine WP.mono (copyPt_ok hsv backIn h.apart backApart) fun t ⟨tx,ty,tz,kt,ot⟩ => ?_
  refine ⟨(keep.mono (by simp)).trans ((kv.mono (by simp)).trans (kt.mono (by simp))),?_,?_,?_⟩
  · apply ((Outs.unch outs).trans ((Outs.unch ov).trans (Outs.unch ot))).cover
    intro w hw
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with (rfl|rfl|rfl)|((rfl|rfl)|(rfl|rfl|rfl))
    all_goals simp only [loopWrites,List.mem_cons,List.not_mem_nil,or_false]
    all_goals first
      | exact ⟨_,Or.inl rfl,Nat.le_refl _,Nat.le_refl _⟩
      | exact ⟨_,Or.inr (Or.inl rfl),Nat.le_refl _,Nat.le_refl _⟩
      | exact ⟨_,Or.inr (Or.inr (Or.inl rfl)),Nat.le_refl _,Nat.le_refl _⟩
      | exact ⟨(Impl.Weierstrass.Point.oAt K.L.M.n,72*K.L.M.n),
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
          lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide)⟩
      | exact ⟨(Impl.Weierstrass.Point.ownAt K.L.M.n,4096-Impl.Weierstrass.Point.ownAt K.L.M.n),
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))),Nat.le_refl _,Nat.le_refl _⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    rw [tx,ty,tz]
    simpa only [TCombCfg.O,ptAt,enc_0,enc_1,enc_2] using And.intro (lv 0 (by decide)) (And.intro (lv 1 (by decide)) (lv 2 (by decide)))
  · rw [tx,ty,tz]
    have ev := eqv
    simp only [Eb,enc_0,enc_1,enc_2] at ev
    simp only [TCombCfg.O,ptAt]
    rw [ev]
    simp only [ptVal,Eb,enc_3,enc_4,enc_5,enc_6,enc_7,enc_8,enc_9,enc_10,Bool.false_eq_true,↓reduceIte]
    rw [px,py,pz]
    have oa := other (Impl.Weierstrass.Point.aAt K.L.M.n) (by simp)
    have ob := other (Impl.Weierstrass.Point.b3At K.L.M.n) (by simp)
    have ox := other K.Q.x (by simp)
    have oy := other K.Q.y (by simp)
    have oz := other K.Q.z (by simp)
    simp only [TCombCfg.Q,ptAt] at ox oy oz
    rw [oa,ob,ox,oy,oz]

end VG.Proof.Weierstrass.Arm.TComb
