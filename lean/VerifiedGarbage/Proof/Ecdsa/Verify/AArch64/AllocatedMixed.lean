import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedArithmetic

namespace VG.Proof.Ecdsa.Verify.AArch64.Allocated
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

/-- Complete mixed addition preserves the infinity, doubling and opposite branches. -/
theorem mixedAdd_ok (raw : RawCorrect) (hC : Law C) (ha : AM3 C)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hOne : K.one<C.p)
    {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base 8192 C.p Sl V E s) (hV : ∀ x∈rcbR K.S K.R K.E,x∈V)
    {P Q : Point C} (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hJP : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) P)
    (hJQ : InvJ C (E K.E.x) (E K.E.y) (E K.E.z) Q) (hAff : E K.E.z=1) :
    WP isa VG.Impl.Ecdsa.Verify.AArch64.P256Allocated.mixedAdd s
      (PointPost base V K.D (add P Q) s) := by
  let hL := JointLayout.layout.lay
  let hAl := JointLayout.layout.aligned
  have hA := apart
  have hSl : ∀ x∈rcbW K.S K.D++rcbR K.S K.R K.E,Sl x := by decide +kernel
  have hsize : 8192≤8192 := Nat.le_refl _
  rw [VG.Impl.Ecdsa.Verify.AArch64.P256Allocated.mixedAdd]
  apply fieldBranch_ok hL hAl hm hI (hV K.R.z (by simp [rcbR]))
  · intro a ia ka hz
    have hp := (hJP.z_zero_iff hC).mp hz
    rw [hp]
    exact WP.mono (copyPointJ_ok hL hAl hA hSl ia hV hJQ)
      (fun t ht => PointPost.of_jac (ht.prefix (ka.mono (by simp))))
  · intro a ia ka hpz
    have hqz : E K.E.z ≠ 0 := by rw [hAff]; exact hC.one_ne_zero
    apply WP.seq
    refine WP.mono (jacMixedInit_ok hL hAl hSl ia hV) fun b ⟨kb,ib⟩ => ?_
    apply WP.seq
    refine WP.mono (mixedHead_ok raw ib hV) fun c ⟨kc,ic,eh,er⟩ => ?_
    let EH := runOps (jacMixedHead K.S K.R K.E) (jacMixedInit K.S K.R E)
    have hkeep := (liftProg ka (by simp)).trans ((liftProg kb (by decide +kernel)).trans kc)
    have hpkeep : ∀ x ∈ rcbR K.S K.R K.E, EH x = E x := fun x hx => jacMixedHead_readonly hA E hx
    have jp : InvJ C (EH K.R.x) (EH K.R.y) (EH K.R.z) P := by
      rw [hpkeep _ (by simp [rcbR]),hpkeep _ (by simp [rcbR]),hpkeep _ (by simp [rcbR])]
      exact hJP
    have oldV : ∀ x ∈ V, x ∈ validAfter (jacMixedHead K.S K.R K.E) (K.S.t4::K.S.t2::V) :=
      fun x hx => (mem_validAfter _ _).mpr (Or.inl (by simp [hx]))
    have hv : ∀ x ∈ rcbR K.S K.R K.R, x ∈ validAfter (jacMixedHead K.S K.R K.E) (K.S.t4::K.S.t2::V) :=
      fun x hx => oldV x (hV x (rcbR_self_mem _ _ _ hx))
    apply fieldBranch_ok hL hAl hm ic (a := K.S.t3) (by
      rw [mem_validAfter]; right; simp [jacMixedHead,FOp.out])
    · intro d id kd hz
      have hx : E K.E.x*(E K.R.z*E K.R.z)-E K.R.x*(E K.E.z*E K.E.z)=0 := by simpa only [hAff,Lean.Grind.Semiring.mul_one] using eh.symm.trans hz
      apply fieldBranch_ok hL hAl hm id (a := K.S.t5) (by
        rw [mem_validAfter]; right; simp [jacMixedHead,FOp.out])
      · intro e ie ke hrz
        have hy : E K.E.y*E K.R.z*(E K.R.z*E K.R.z)-E K.R.y*E K.E.z*(E K.E.z*E K.E.z)=0 := by simpa only [hAff,Lean.Grind.Semiring.mul_one] using er.symm.trans hrz
        have hpq := hJP.same hC hJQ hpz hqz hx hy
        have hdA : RcbApart K.S K.R K.R K.D := ⟨hA.nodup,fun x hx => hA.apart x (rcbR_self_mem _ _ _ hx)⟩
        have hdSl : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.R K.R, Sl x := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hSl x (List.mem_append_left _ hx)
          · exact hSl x (List.mem_append_right _ (rcbR_self_mem _ _ _ hx))
        rw [←hpq]
        refine WP.mono (Forward.double_ok Forward.Production.cases hL hAl (callOf_small (by decide)) hm hC ha hdA hdSl ie hv hP jp) fun t ⟨kt,it,jt⟩ => ?_
        exact (PointPost.sub ⟨_,liftProg kt (by decide +kernel),it,jt⟩ oldV).prefix
          (hkeep.trans ((liftProg kd (by simp)).trans (liftProg ke (by simp))))
      · intro e ie ke hrz
        have hy : E K.E.y*E K.R.z*(E K.R.z*E K.R.z)-E K.R.y*E K.E.z*(E K.E.z*E K.E.z)≠0 := by
          intro he
          apply hrz
          rw [er]
          simpa only [hAff,Lean.Grind.Semiring.mul_one] using he
        have hadd := hJP.opposite hC hP hQ hJQ hpz hqz hx hy
        rw [hadd]
        refine WP.mono (infinityPoint_ok (K:=K) (o:=K.D) hL hAl
          (fun x hx => hSl x (by
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
            rcases hx with rfl | rfl | rfl <;> simp [rcbW])) ie hOne) fun t ht => ?_
        exact ((PointPost.of_jac ht).sub oldV).prefix
          (hkeep.trans ((liftProg kd (by simp)).trans (liftProg ke (by simp))))
    · intro d id kd hz
      have hh : E K.E.x*(E K.R.z*E K.R.z)-E K.R.x*(E K.E.z*E K.E.z)≠0 := by
        intro he
        apply hz
        rw [eh]
        simpa only [hAff,Lean.Grind.Semiring.mul_one] using he
      refine WP.mono (mixedTail_ok raw id hV) fun t ⟨kt,it,ht⟩ => ?_
      have jt := hJP.add_ne hC ha hP hQ hJQ hpz hqz hh
      dsimp only at jt
      rw [hAff,←ht] at jt
      exact PointPost.prefix ⟨_,kt,it,jt⟩ (hkeep.trans (liftProg kd (by simp)))


end VG.Proof.Ecdsa.Verify.AArch64.Allocated
