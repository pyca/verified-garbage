import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open Spec.Weierstrass

/-- The two copied coordinates are initialized before the mixed formula reads them. -/
theorem jacMixedInit_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    {S : RcbSlots} {p q o : Pt} (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (.block (copy M.n S.t2 p.x ++ copy M.n S.t4 p.y)) s fun t =>
      ProgKeep M base (rcbW S o) s t ∧
      Inv M base size m Sl (S.t4::S.t2::V) (jacMixedInit S p E) t := by
  rw [WP.block_append_iff]
  refine WP.mono (copyField_ok hL hAl hI (hSl S.t2 (by simp [rcbW]))
    (hV p.x (by simp [rcbR]))) fun a ⟨ka,ia⟩ => ?_
  refine WP.mono (copyField_ok hL hAl ia (hSl S.t4 (by simp [rcbW]))
    (List.mem_cons_of_mem _ (hV p.y (by simp [rcbR])))) fun t ⟨kt,it⟩ =>
    ⟨(progKeep_of_op ka (by simp [rcbW])).trans (progKeep_of_op kt (by simp [rcbW])),it⟩

/-- The mixed header's field operations and its two exceptional-case values. -/
theorem jacMixedHead_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod m (2^(64*M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl (S.t4::S.t2::V) (jacMixedInit S p E) s)
    (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (.block (fprog M (jacMixedHead S p q))) s fun t =>
      ProgKeep M base (rcbW S o) s t ∧
      Inv M base size m Sl (validAfter (jacMixedHead S p q) (S.t4::S.t2::V))
        (runOps (jacMixedHead S p q) (jacMixedInit S p E)) t ∧
      runOps (jacMixedHead S p q) (jacMixedInit S p E) S.t3 = E q.x*(E p.z*E p.z)-E p.x ∧
      runOps (jacMixedHead S p q) (jacMixedInit S p E) S.t5 = E q.y*E p.z*(E p.z*E p.z)-E p.y := by
  rw [jacMixedHead_eq S p q o]
  have hr := readsOk_rename (rcbσ S p q o)
    (show readsOk jacMixedHeadN [4,2,9,10,11,12,13,14,15,16] = true by decide)
  have hr' : readsOk (ofN jacMixedHeadN S p q o) (S.t4::S.t2::V) = true :=
    readsOk_mono hr (by
      intro x hx
      change x ∈ S.t4::S.t2::rcbR S p q at hx
      simp only [List.mem_cons] at hx ⊢
      rcases hx with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (hV x h)))
  refine WP.mono (ofN_partial_ok hL hAl hm
    (show ∀ op ∈ jacMixedHeadN, op.out<9 by decide) hA hSl hI hr')
    fun t ⟨kt,it,he⟩ => ⟨kt,it,?_,?_⟩
  · have h := he 3
    rw [jacMixedInit_rename hA] at h
    exact h.trans (jacMixedHeadN_run (fun i => E (rcbσ S p q o i))).1
  · have h := he 5
    rw [jacMixedInit_rename hA] at h
    exact h.trans (jacMixedHeadN_run (fun i => E (rcbσ S p q o i))).2

/-- Read-only coordinates survive the two initialization copies and header. -/
theorem jacMixedHead_readonly {F : Type _} [Lean.Grind.CommRing F]
    {S : RcbSlots} {p q o : Pt} (hA : RcbApart S p q o) (E : Nat → F)
    {x : Nat} (hx : x ∈ rcbR S p q) :
    runOps (jacMixedHead S p q) (jacMixedInit S p E) x = E x := by
  have hn2 : x≠S.t2 := fun he => hA.apart x hx (by rw [he]; simp [rcbW])
  have hn4 : x≠S.t4 := fun he => hA.apart x hx (by rw [he]; simp [rcbW])
  rw [runOps_of_not_out]
  · simp only [jacMixedInit,Function.update_of_ne hn2,Function.update_of_ne hn4]
  · intro op hop he
    have ho : op.out ∈ rcbW S o := by
      rw [jacMixedHead_eq S p q o] at hop
      obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hop
      rw [FOp.out_rename]
      exact rcbσ_out S p q o ((show ∀ n ∈ jacMixedHeadN, n.out<9 by decide) n hn)
    exact hA.apart x hx (he ▸ ho)

/-- The nonexceptional mixed tail returns Jacobian addition with affine z=1. -/
theorem jacMixedTail_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod m (2^(64*M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl (validAfter (jacMixedHead S p q) (S.t4::S.t2::V))
      (runOps (jacMixedHead S p q) (jacMixedInit S p E)) s)
    (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (.block (fprog M (jacMixedTail S p q o))) s fun t =>
      ProgKeep M base (rcbW S o) s t ∧
      Inv M base size m Sl ([o.x,o.y,o.z]++V)
        (runOps (jacMixedHead S p q ++ jacMixedTail S p q o) (jacMixedInit S p E)) t ∧
      (runOps (jacMixedHead S p q ++ jacMixedTail S p q o) (jacMixedInit S p E) o.x,
       runOps (jacMixedHead S p q ++ jacMixedTail S p q o) (jacMixedInit S p E) o.y,
       runOps (jacMixedHead S p q ++ jacMixedTail S p q o) (jacMixedInit S p E) o.z) =
        jacAddF (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) 1 := by
  let N := jacMixedHeadN ++ jacMixedTailN
  have he : jacMixedHead S p q ++ jacMixedTail S p q o = ofN N S p q o := by
    rw [jacMixedHead_eq S p q o,jacMixedTail_eq]
    simp only [N,ofN,List.map_append]
  have hN : ∀ op ∈ N, op.out<9 := by decide
  have hr := readsOk_rename (rcbσ S p q o)
    (show readsOk N [4,2,9,10,11,12,13,14,15,16] = true by decide)
  have hr' : readsOk (ofN N S p q o) (S.t4::S.t2::V) = true := readsOk_mono hr (by
    intro x hx
    change x ∈ S.t4::S.t2::rcbR S p q at hx
    simp only [List.mem_cons] at hx ⊢
    rcases hx with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (hV x h)))
  rw [←he,readsOk_append,Bool.and_eq_true] at hr'
  have hw : ∀ op ∈ jacMixedTail S p q o, op.out ∈ rcbW S o := by
    intro op hop
    have hop' : op ∈ ofN N S p q o := he ▸ List.mem_append_right _ hop
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hop'
    rw [FOp.out_rename]
    exact rcbσ_out S p q o (hN n hn)
  have hv : ∀ x ∈ [o.x,o.y,o.z], x ∈ (jacMixedTail S p q o).map FOp.out := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [jacMixedTail,jacTail,FOp.out]
  refine WP.mono (fprog_ok hL hAl hm _ hI
    (fun op hop x hx => hSl x (ofN_slots op (he ▸ List.mem_append_right _ hop) x hx)) hr'.2)
    fun t ⟨kt,it⟩ => ⟨kt.mono ?_,?_,?_⟩
  · intro w hw'
    obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hw'
    exact hw op hop
  · rw [runOps_append]
    apply it.sub
    intro x hx
    rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (hv x hx)
    · exact Or.inl ((mem_validAfter _ _).mpr (Or.inl (by simp [hx])))
  · rw [he]
    have hren := runOps_rename (rcbσ S p q o) N (jacMixedInit S p E)
      (fun op hop => hA.inj (hN op hop))
    rw [jacMixedInit_rename hA] at hren
    exact (congrArg₂ Prod.mk (congrFun hren 6)
      (congrArg₂ Prod.mk (congrFun hren 7) (congrFun hren 8))).trans
      (jacMixedN_run (fun i => E (rcbσ S p q o i)))

theorem jacMixedAdd_ok {K : WinCfg} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    {p q o : Pt} (hA : RcbApart K.S p q o)
    (hSl : ∀ x ∈ rcbW K.S o ++ rcbR K.S p q, Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s) (hV : ∀ x ∈ rcbR K.S p q, x ∈ V)
    (hOne : K.one < C.p) {P Q : Point C} (hP : onCurve C P = true) (hQ : onCurve C Q = true)
    (hJP : InvJ C (E p.x) (E p.y) (E p.z) P) (hJQ : InvJ C (E q.x) (E q.y) (E q.z) Q) (hAff : E q.z=1) :
    WP isa (Jacobian.jacMixedAdd K p q o) s
      (JacPost K.M K.S base size C Sl V o (Spec.Weierstrass.add P Q) s) := by
  rw [Jacobian.jacMixedAdd]
  apply fieldBranch_ok hL hAl hm hI (hV p.z (by simp [rcbR]))
  · intro a ia ka hz
    have hp := (hJP.z_zero_iff hC).mp hz
    rw [hp]
    exact WP.mono (copyPointJ_ok hL hAl hA hSl ia hV hJQ)
      (fun t ht => ht.prefix (ka.mono (by simp)))
  · intro a ia ka hpz
    have hqz : E q.z ≠ 0 := by rw [hAff]; exact hC.one_ne_zero
    apply WP.seq
    refine WP.mono (jacMixedInit_ok hL hAl hSl ia hV) fun b ⟨kb,ib⟩ => ?_
    apply WP.seq
    apply (fprogB_wp _ _).mpr
    refine WP.mono (jacMixedHead_ok hL hAl hm hA hSl ib hV) fun c ⟨kc,ic,eh,er⟩ => ?_
    let EH := runOps (jacMixedHead K.S p q) (jacMixedInit K.S p E)
    have hkeep := (ka.mono (W' := rcbW K.S o) (by simp)).trans
      ((kb.mono (by simp)).trans kc)
    have hpkeep : ∀ x ∈ rcbR K.S p q, EH x = E x := fun x hx => jacMixedHead_readonly hA E hx
    have jp : InvJ C (EH p.x) (EH p.y) (EH p.z) P := by
      rw [hpkeep _ (by simp [rcbR]),hpkeep _ (by simp [rcbR]),hpkeep _ (by simp [rcbR])]
      exact hJP
    have oldV : ∀ x ∈ V, x ∈ validAfter (jacMixedHead K.S p q) (K.S.t4::K.S.t2::V) :=
      fun x hx => (mem_validAfter _ _).mpr (Or.inl (by simp [hx]))
    have hv : ∀ x ∈ rcbR K.S p p, x ∈ validAfter (jacMixedHead K.S p q) (K.S.t4::K.S.t2::V) :=
      fun x hx => oldV x (hV x (rcbR_self_mem _ _ _ hx))
    apply fieldBranch_ok hL hAl hm ic (a := K.S.t3) (by
      rw [mem_validAfter]; right; simp [jacMixedHead,FOp.out])
    · intro d id kd hz
      have hx : E q.x*(E p.z*E p.z)-E p.x*(E q.z*E q.z)=0 := by simpa only [hAff,Lean.Grind.Semiring.mul_one] using eh.symm.trans hz
      apply fieldBranch_ok hL hAl hm id (a := K.S.t5) (by
        rw [mem_validAfter]; right; simp [jacMixedHead,FOp.out])
      · intro e ie ke hrz
        have hy : E q.y*E p.z*(E p.z*E p.z)-E p.y*E q.z*(E q.z*E q.z)=0 := by simpa only [hAff,Lean.Grind.Semiring.mul_one] using er.symm.trans hrz
        have hpq := hJP.same hC hJQ hpz hqz hx hy
        have hdA : RcbApart K.S p p o := ⟨hA.nodup,fun x hx => hA.apart x (rcbR_self_mem _ _ _ hx)⟩
        have hdSl : ∀ x ∈ rcbW K.S o ++ rcbR K.S p p, Sl x := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hSl x (List.mem_append_left _ hx)
          · exact hSl x (List.mem_append_right _ (rcbR_self_mem _ _ _ hx))
        rw [←hpq]
        refine WP.mono (jacDouble_ok hL hAl hm hC ha hdA hdSl ie hv hP jp) fun t ⟨kt,it,jt⟩ => ?_
        exact (JacPost.sub ⟨_,kt,it,jt⟩ oldV).prefix
          (hkeep.trans ((kd.mono (by simp)).trans (ke.mono (by simp))))
      · intro e ie ke hrz
        have hy : E q.y*E p.z*(E p.z*E p.z)-E p.y*E q.z*(E q.z*E q.z)≠0 := by
          intro he
          apply hrz
          rw [er]
          simpa only [hAff,Lean.Grind.Semiring.mul_one] using he
        have hadd := hJP.opposite hC hP hQ hJQ hpz hqz hx hy
        rw [hadd]
        refine WP.mono (infinityPoint_ok hL hAl
          (fun x hx => hSl x (by
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
            rcases hx with rfl | rfl | rfl <;> simp [rcbW])) ie hOne) fun t ht => ?_
        exact (JacPost.sub ht oldV).prefix
          (hkeep.trans ((kd.mono (by simp)).trans (ke.mono (by simp))))
    · intro d id kd hz
      have hh : E q.x*(E p.z*E p.z)-E p.x*(E q.z*E q.z)≠0 := by
        intro he
        apply hz
        rw [eh]
        simpa only [hAff,Lean.Grind.Semiring.mul_one] using he
      apply (fprogB_wp _ _).mpr
      refine WP.mono (jacMixedTail_ok hL hAl hm hA hSl id hV) fun t ⟨kt,it,ht⟩ => ?_
      have jt := hJP.add_ne hC ha hP hQ hJQ hpz hqz hh
      dsimp only at jt
      rw [hAff,←ht] at jt
      exact JacPost.prefix ⟨_,kt,it,jt⟩ (hkeep.trans (kd.mono (by simp)))

end VG.Proof.Weierstrass.AArch64
