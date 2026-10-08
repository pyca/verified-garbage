import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedAddField

namespace VG.Proof.Weierstrass.AArch64.CachedField
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass

/-- Complete Jacobian addition on public data, including all exceptional cases. -/
theorem add_ok {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl) (hnc : Mont.callOf K.M = none)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hsize : 8192≤size) (hC : Law C) (ha : AM3 C)
    (hSlots : ∀ x∈slots,Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s) (hInputs : ∀ x∈inputs,x∈V)
    (h2 : E 5400=E K.E.z*E K.E.z) (h3 : E 5432=E K.E.z*(E K.E.z*E K.E.z))
    (hOne : K.one < C.p) {P Q : Point C} (hP : onCurve C P = true) (hQ : onCurve C Q = true)
    (hJP : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) P) (hJQ : InvJ C (E K.E.x) (E K.E.y) (E K.E.z) Q) :
    WP isa (CachedJac.add K ops) s
      (JacPost K.M K.S base size C Sl V K.D (Spec.Weierstrass.add P Q) s) := by
  have hA : RcbApart K.S K.R K.E K.D := by exact ⟨by decide +kernel,by decide +kernel⟩
  have hSl : ∀ x∈rcbW K.S K.D ++ rcbR K.S K.R K.E,Sl x := by
    intro x hx
    exact hSlots x (by simpa only [slots,inputs,List.append_assoc] using List.mem_append_left [5400,5432] hx)
  have hV : ∀ x∈rcbR K.S K.R K.E,x∈V := fun x hx => hInputs x (List.mem_append_left _ hx)
  rw [CachedJac.add]
  change WP isa _ s _
  apply fieldBranch_ok hL hAl hm hI (hV K.R.z (by simp [rcbR]))
  · intro a ia ka hz
    have hp := (hJP.z_zero_iff hC).mp hz
    rw [hp]
    exact WP.mono (copyPointJ_ok hL hAl hA hSl ia hV hJQ)
      (fun t ht => ht.prefix (ka.mono (by simp)))
  · intro a ia ka hpz
    apply fieldBranch_ok hL hAl hm ia (hV K.E.z (by simp [rcbR]))
    · intro b ib kb hz
      have hq := (hJQ.z_zero_iff hC).mp hz
      have hs : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.E K.R, Sl x := by
        intro x hx
        rw [List.mem_append,rcbR_swap_mem] at hx
        exact hSl x (List.mem_append.mpr hx)
      have hv : ∀ x ∈ rcbR K.S K.E K.R, x ∈ V := fun x hx => hV x ((rcbR_swap_mem _ _ _ _).mp hx)
      have hadd : Spec.Weierstrass.add P Q = P := by rw [hq]; cases P <;> rfl
      rw [hadd]
      exact WP.mono (copyPointJ_ok hL hAl hA.swap hs ib hv hJP)
        (fun t ht => (ht.prefix (kb.mono (by simp))).prefix (ka.mono (by simp)))
    · intro b ib kb hqz
      apply WP.seq
      refine WP.mono (head_ok hL hAl hm hsize hSlots ib hInputs h2 h3) fun c ⟨kc,ic,eh,er⟩ => ?_
      let EH := runOps head E
      have hkeep := (ka.mono (W' := rcbW K.S K.D) (by simp)).trans
        ((kb.mono (by simp)).trans kc)
      have hpkeep : ∀ x ∈ rcbR K.S K.R K.E, EH x = E x := fun x hx => head_readonly E (List.mem_append_left _ hx)
      have jp : InvJ C (EH K.R.x) (EH K.R.y) (EH K.R.z) P := by
        rw [hpkeep _ (by simp [rcbR]),hpkeep _ (by simp [rcbR]),hpkeep _ (by simp [rcbR])]
        exact hJP
      have oldV : ∀ x ∈ V, x ∈ validAfter head V :=
        fun x hx => (mem_validAfter _ _).mpr (Or.inl hx)
      have hv : ∀ x ∈ rcbR K.S K.R K.R, x ∈ validAfter head V :=
        fun x hx => oldV x (hV x (rcbR_self_mem _ _ _ hx))
      apply fieldBranch_ok hL hAl hm ic (a := K.S.t3) (by
        rw [mem_validAfter]; right; decide +kernel)
      · intro d id kd hz
        have hx : E K.E.x*(E K.R.z*E K.R.z)-E K.R.x*(E K.E.z*E K.E.z)=0 := eh.symm.trans hz
        apply fieldBranch_ok hL hAl hm id (a := K.S.t5) (by
          rw [mem_validAfter]; right; decide +kernel)
        · intro e ie ke hrz
          have hy : E K.E.y*E K.R.z*(E K.R.z*E K.R.z)-E K.R.y*E K.E.z*(E K.E.z*E K.E.z)=0 := er.symm.trans hrz
          have hpq := hJP.same hC hJQ hpz hqz hx hy
          have hdA : RcbApart K.S K.R K.R K.D := ⟨hA.nodup,fun x hx => hA.apart x (rcbR_self_mem _ _ _ hx)⟩
          have hdSl : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.R K.R, Sl x := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hSl x (List.mem_append_left _ hx)
            · exact hSl x (List.mem_append_right _ (rcbR_self_mem _ _ _ hx))
          rw [←hpq]
          dsimp only [ops]
          refine WP.mono (Forward.double_ok Forward.Production.cases hL hAl hnc hm hC ha hdA hdSl ie hv hP jp) fun t ⟨kt,it,jt⟩ => ?_
          exact (JacPost.sub ⟨_,kt,it,jt⟩ oldV).prefix
            (hkeep.trans ((kd.mono (by simp)).trans (ke.mono (by simp))))
        · intro e ie ke hrz
          have hy : E K.E.y*E K.R.z*(E K.R.z*E K.R.z)-E K.R.y*E K.E.z*(E K.E.z*E K.E.z)≠0 := fun he => hrz (er.trans he)
          have hadd := hJP.opposite hC hP hQ hJQ hpz hqz hx hy
          rw [hadd]
          refine WP.mono (infinityPoint_ok hL hAl
            (fun x hx => hSl x (by
              simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
              rcases hx with rfl | rfl | rfl <;> simp [rcbW])) ie hOne) fun t ht => ?_
          exact (JacPost.sub ht oldV).prefix
            (hkeep.trans ((kd.mono (by simp)).trans (ke.mono (by simp))))
      · intro d id kd hz
        have hh : E K.E.x*(E K.R.z*E K.R.z)-E K.R.x*(E K.E.z*E K.E.z)≠0 := fun he => hz (eh.trans he)
        refine WP.mono (tail_ok hL hAl hm hsize hSlots id hInputs h2 h3) fun t ⟨kt,it,ht⟩ => ?_
        have jt := hJP.add_ne hC ha hP hQ hJQ hpz hqz hh
        dsimp only at jt
        rw [←ht] at jt
        exact JacPost.prefix ⟨_,kt,it,jt⟩ (hkeep.trans (kd.mono (by simp)))

end VG.Proof.Weierstrass.AArch64.CachedField
