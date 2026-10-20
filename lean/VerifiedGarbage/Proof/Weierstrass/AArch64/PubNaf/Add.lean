module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import VerifiedGarbage.Proof.Weierstrass.JacMul
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# Jacobian addition and doubling whose products may be calls

`jacAddB_ok` is `jacAdd_ok` for products that are calls of a function (the
slots of the formulas below the function's working space, `Low`), and a
modulus other than P-256's measured layouts, whose exceptional doubling is
`dblJMul` (`VerifyDouble.double`). `dblB_ok` is a doubling `dblJ` or
`dblJMul`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64
open VG.Impl.Weierstrass VG.Proof.Mont.AArch64 VG.Proof.Mont
open Spec.Weierstrass

/-- Only four-word moduli take P-256's forwarded doubling. -/
theorem verifyDouble_eq {m : Mod} (hn : m.n ≠ 4) (S : RcbSlots) (p o : Pt) :
    VG.Impl.P256.VerifyDouble.double m S p o = fprogB m (dblJMul S p o) := by
  unfold VG.Impl.P256.VerifyDouble.double
  refine ite_eq_right_iff.mpr fun h => absurd ?_ hn
  obtain ⟨rfl, -⟩ := h
  rfl

/-- `ofN_partial_ok` for products that may be calls. -/
theorem ofN_partialB_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod m (2 ^ (64 * M.n))) {N : List FOp}
    (hN : ∀ op ∈ N, op.out < 9) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x)
    (hLow : Low M (rcbW S o ++ rcbR S p q))
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s)
    (hR : readsOk (ofN N S p q o) V = true) :
    WP isa (fprogB M (ofN N S p q o)) s fun s' =>
      ProgKeep M base (rcbW S o) s s' ∧
      Inv M base size m Sl (validAfter (ofN N S p q o) V)
        (runOps (ofN N S p q o) E) s' ∧
      ∀ i, runOps (ofN N S p q o) E (rcbσ S p q o i) =
        runOps N (fun j => E (rcbσ S p q o j)) i := by
  refine WP.mono (fprogB_ok hL hAl hm _ hI
    (fun op hop x hx => hSl x (ofN_slots op hop x hx))
    (fun op hop => hLow.mono (ofN_slots op hop)) hR) fun s' ⟨hk, hi⟩ => ⟨hk.mono ?_, hi, ?_⟩
  · intro w hw
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    obtain ⟨op', hop', rfl⟩ := List.mem_map.mp hop
    rw [FOp.out_rename]
    exact rcbσ_out S p q o (hN op' hop')
  · intro i
    exact congrFun (runOps_rename (rcbσ S p q o) N E
      (fun op hop => hA.inj (hN op hop))) i

theorem jacHeadB_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod m (2 ^ (64 * M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x)
    (hLow : Low M (rcbW S o ++ rcbR S p q))
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (fprogB M (jacHead S p q)) s fun s' =>
      ProgKeep M base (rcbW S o) s s' ∧
      Inv M base size m Sl (validAfter (jacHead S p q) V)
        (runOps (jacHead S p q) E) s' ∧
      runOps (jacHead S p q) E S.t3 = E q.x * (E p.z * E p.z) - E p.x * (E q.z * E q.z) ∧
      runOps (jacHead S p q) E S.t5 = E q.y * E p.z * (E p.z * E p.z) -
        E p.y * E q.z * (E q.z * E q.z) := by
  rw [jacHead_eq S p q o]
  have hr : readsOk (ofN jacHeadN S p q o) V = true :=
    readsOk_mono (readsOk_rename (rcbσ S p q o)
      (show readsOk jacHeadN [9,10,11,12,13,14,15,16] = true by decide)) hV
  refine WP.mono (ofN_partialB_ok hL hAl hm
    (show ∀ op ∈ jacHeadN, op.out < 9 by decide) hA hSl hLow hI hr)
    fun s' ⟨hk, hi, he⟩ => ⟨hk, hi, ?_, ?_⟩
  · exact (he 3).trans (jacHeadN_run (fun j => E (rcbσ S p q o j))).2.1
  · exact (he 5).trans (jacHeadN_run (fun j => E (rcbσ S p q o j))).2.2.2

theorem jacTailB_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod m (2 ^ (64 * M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x)
    (hLow : Low M (rcbW S o ++ rcbR S p q))
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl (validAfter (jacHead S p q) V)
      (runOps (jacHead S p q) E) s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (fprogB M (jacTail S p q o)) s fun s' =>
      ProgKeep M base (rcbW S o) s s' ∧
      Inv M base size m Sl ([o.x,o.y,o.z] ++ V)
        (runOps (jacHead S p q ++ jacTail S p q o) E) s' ∧
      (runOps (jacHead S p q ++ jacTail S p q o) E o.x,
       runOps (jacHead S p q ++ jacTail S p q o) E o.y,
       runOps (jacHead S p q ++ jacTail S p q o) E o.z) =
        jacAddF (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) (E q.z) := by
  have he : jacHead S p q ++ jacTail S p q o = ofN (jacHeadN ++ jacTailN) S p q o := by
    rw [jacHead_eq S p q o, jacTail_eq]
    simp only [ofN, List.map_append]
  have hr := readsOk_mono (ofN_readsOk jacAddN_ok S p q o) hV
  rw [← he, readsOk_append, Bool.and_eq_true] at hr
  have hw : ∀ op ∈ jacTail S p q o, op.out ∈ rcbW S o := by
    intro op hop
    exact ofN_out jacAddN_ok op (he ▸ List.mem_append_right _ hop)
  have hv : ∀ x ∈ [o.x,o.y,o.z], x ∈ (jacTail S p q o).map FOp.out := by
    simp only [jacTail, List.map_cons, List.map_nil, FOp.out, List.mem_cons, List.not_mem_nil, or_false]
    intro x hx
    rcases hx with rfl | rfl | rfl <;> simp
  refine WP.mono (fprogB_ok hL hAl hm _ hI
    (fun op hop x hx => hSl x (ofN_slots op (he ▸ List.mem_append_right _ hop) x hx))
    (fun op hop => hLow.mono (ofN_slots op (he ▸ List.mem_append_right _ hop))) hr.2)
    fun s' ⟨hk, hi⟩ => ⟨hk.mono ?_, ?_, ?_⟩
  · intro w hw'
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw'
    exact hw op hop
  · rw [runOps_append]
    apply hi.sub
    intro x hx
    rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (hv x hx)
    · exact Or.inl ((mem_validAfter _ _).mpr (Or.inl hx))
  · rw [he]
    exact (congrArg₂ Prod.mk (ofN_run jacAddN_ok hA E 6)
      (congrArg₂ Prod.mk (ofN_run jacAddN_ok hA E 7) (ofN_run jacAddN_ok hA E 8))).trans
      (jacAddN_run (fun i => E (rcbσ S p q o i)))

/-- A Jacobian doubling, `dblJMul` (`direct`) or `dblJ`, whose products may be calls. -/
theorem dblB_ok (direct : Bool) {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod C.p (2^(64*M.n))) (hC : Law C) (ha : AM3 C)
    {S : RcbSlots} {p o : Pt} (hA : RcbApart S p p o)
    (hSl : ∀ x ∈ rcbW S o ++ rcbR S p p, Sl x) (hLow : Low M (rcbW S o ++ rcbR S p p))
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv M base size C.p Sl V E s)
    (hV : ∀ x ∈ rcbR S p p, x ∈ V) {P : Point C}
    (hP : onCurve C P = true) (hJ : InvJ C (E p.x) (E p.y) (E p.z) P) :
    WP isa (fprogB M (if direct then dblJMul S p o else dblJ S p o)) s
      (JacPost M S base size C Sl V o (Spec.Weierstrass.add P P) s) := by
  have he : (if direct then dblJMul S p o else dblJ S p o) = ofN (dblJChoiceN direct) S p p o := by
    cases direct
    · exact dblJChoice_eq false S p o
    · exact dblJChoice_eq true S p o
  rw [he]
  refine WP.mono (ofN_ok hL hAl hm (dblJChoiceN_ok direct) hA hSl hLow hI hV)
    fun t ⟨hk, hi, hv⟩ => ⟨_, hk, hi, ?_⟩
  exact InvJ.dbl' hC ha hP hJ (hv.trans (dblJChoiceN_run direct _))

/-- Complete Jacobian addition on public data, including all exceptional
cases, for products that may be calls and a modulus of other than four words. -/
theorem jacAddB_ok {K : WinCfg} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl) (hn4 : K.M.n ≠ 4)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    {p q o : Pt} (hA : RcbApart K.S p q o)
    (hSl : ∀ x ∈ rcbW K.S o ++ rcbR K.S p q, Sl x) (hLow : Low K.M (rcbW K.S o ++ rcbR K.S p q))
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s) (hV : ∀ x ∈ rcbR K.S p q, x ∈ V)
    (hOne : K.one < C.p) {P Q : Point C} (hP : onCurve C P = true) (hQ : onCurve C Q = true)
    (hJP : InvJ C (E p.x) (E p.y) (E p.z) P) (hJQ : InvJ C (E q.x) (E q.y) (E q.z) Q) :
    WP isa (Jacobian.jacAdd K p q o) s
      (JacPost K.M K.S base size C Sl V o (Spec.Weierstrass.add P Q) s) := by
  rw [Jacobian.jacAdd]
  apply fieldBranch_ok hL hAl hm hI (hV p.z (by simp [rcbR]))
  · intro a ia ka hz
    have hp := (hJP.z_zero_iff hC).mp hz
    rw [hp]
    exact WP.mono (copyPointJ_ok hL hAl hA hSl ia hV hJQ)
      (fun t ht => ht.prefix (ka.mono (by simp)))
  · intro a ia ka hpz
    apply fieldBranch_ok hL hAl hm ia (hV q.z (by simp [rcbR]))
    · intro b ib kb hz
      have hq := (hJQ.z_zero_iff hC).mp hz
      have hs : ∀ x ∈ rcbW K.S o ++ rcbR K.S q p, Sl x := by
        intro x hx
        rw [List.mem_append, rcbR_swap_mem] at hx
        exact hSl x (List.mem_append.mpr hx)
      have hv : ∀ x ∈ rcbR K.S q p, x ∈ V := fun x hx => hV x ((rcbR_swap_mem _ _ _ _).mp hx)
      have hadd : Spec.Weierstrass.add P Q = P := by rw [hq]; cases P <;> rfl
      rw [hadd]
      exact WP.mono (copyPointJ_ok hL hAl hA.swap hs ib hv hJP)
        (fun t ht => (ht.prefix (kb.mono (by simp))).prefix (ka.mono (by simp)))
    · intro b ib kb hqz
      apply WP.seq
      refine WP.mono (jacHeadB_ok hL hAl hm hA hSl hLow ib hV) fun c ⟨kc, ic, eh, er⟩ => ?_
      let EH := runOps (jacHead K.S p q) E
      have hkeep := (ka.mono (W' := rcbW K.S o) (by simp)).trans
        ((kb.mono (by simp)).trans kc)
      have hpkeep : ∀ x ∈ rcbR K.S p q, EH x = E x := fun x hx => jacHead_readonly hA E hx
      have jp : InvJ C (EH p.x) (EH p.y) (EH p.z) P := by
        rw [hpkeep _ (by simp [rcbR]), hpkeep _ (by simp [rcbR]), hpkeep _ (by simp [rcbR])]
        exact hJP
      have oldV : ∀ x ∈ V, x ∈ validAfter (jacHead K.S p q) V :=
        fun x hx => (mem_validAfter _ _).mpr (Or.inl hx)
      have hv : ∀ x ∈ rcbR K.S p p, x ∈ validAfter (jacHead K.S p q) V :=
        fun x hx => oldV x (hV x (rcbR_self_mem _ _ _ hx))
      apply fieldBranch_ok hL hAl hm ic (a := K.S.t3) (by
        rw [mem_validAfter]; right; simp [jacHead, FOp.out])
      · intro d id kd hz
        have hx : E q.x*(E p.z*E p.z)-E p.x*(E q.z*E q.z)=0 := eh.symm.trans hz
        apply fieldBranch_ok hL hAl hm id (a := K.S.t5) (by
          rw [mem_validAfter]; right; simp [jacHead, FOp.out])
        · intro e ie ke hrz
          have hy : E q.y*E p.z*(E p.z*E p.z)-E p.y*E q.z*(E q.z*E q.z)=0 := er.symm.trans hrz
          have hpq := hJP.same hC hJQ hpz hqz hx hy
          have hdA : RcbApart K.S p p o := ⟨hA.nodup, fun x hx => hA.apart x (rcbR_self_mem _ _ _ hx)⟩
          have hsub : ∀ x ∈ rcbW K.S o ++ rcbR K.S p p, x ∈ rcbW K.S o ++ rcbR K.S p q := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact List.mem_append_left _ hx
            · exact List.mem_append_right _ (rcbR_self_mem _ _ _ hx)
          rw [← hpq, verifyDouble_eq hn4]
          have hd := dblB_ok true hL hAl hm hC ha hdA (fun x hx => hSl x (hsub x hx))
            (hLow.mono hsub) ie hv hP jp
          simp only [ite_true] at hd
          refine WP.mono hd fun t ht => ?_
          exact (JacPost.sub ht oldV).prefix
            (hkeep.trans ((kd.mono (by simp)).trans (ke.mono (by simp))))
        · intro e ie ke hrz
          have hy : E q.y*E p.z*(E p.z*E p.z)-E p.y*E q.z*(E q.z*E q.z)≠0 := fun he => hrz (er.trans he)
          have hadd := hJP.opposite hC hP hQ hJQ hpz hqz hx hy
          rw [hadd]
          refine WP.mono (infinityPoint_ok hL hAl
            (fun x hx => hSl x (by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              rcases hx with rfl | rfl | rfl <;> simp [rcbW])) ie hOne) fun t ht => ?_
          exact (JacPost.sub ht oldV).prefix
            (hkeep.trans ((kd.mono (by simp)).trans (ke.mono (by simp))))
      · intro d id kd hz
        have hh : E q.x*(E p.z*E p.z)-E p.x*(E q.z*E q.z)≠0 := fun he => hz (eh.trans he)
        refine WP.mono (jacTailB_ok hL hAl hm hA hSl hLow id hV) fun t ⟨kt, it, ht⟩ => ?_
        have jt := hJP.add_ne hC ha hP hQ hJQ hpz hqz hh
        dsimp only at jt
        rw [← ht] at jt
        exact JacPost.prefix ⟨_, kt, it, jt⟩ (hkeep.trans (kd.mono (by simp)))

end VG.Proof.Weierstrass.AArch64
