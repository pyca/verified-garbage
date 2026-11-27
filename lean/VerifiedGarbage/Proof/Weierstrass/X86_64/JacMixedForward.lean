module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.JacMixedForward
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JacAdd
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedAdd
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacDoubleForward
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Block
import Batteries.Logic

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass Spec.Weierstrass

theorem ofN_forward_partial_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2 ^ (64 * M.n))) {N : List FOp}
    (hN : ∀ op ∈ N, op.out < 9) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s)
    (hR : readsOk (ofN N S p q o) V = true) :
    WP isa (ForwardField.programB M (ofN N S p q o)).inline s fun s' =>
      ProgKeep M base (rcbW S o) s s' ∧
      Inv M base size m Sl (validAfter (ofN N S p q o) V)
        (runOps (ofN N S p q o) E) s' ∧
      ∀ i, runOps (ofN N S p q o) E (rcbσ S p q o i) =
        runOps N (fun j => E (rcbσ S p q o j)) i := by
  refine WP.mono (ForwardField.programB_ok hL hm _ hI
    (fun op hop x hx => hSl x (ofN_slots op hop x hx)) hR) fun s' ⟨hk,hi⟩ =>
      ⟨hk.mono ?_,hi,?_⟩
  · intro w hw
    obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hw
    obtain ⟨op',hop',rfl⟩ := List.mem_map.mp hop
    rw [FOp.out_rename]
    exact rcbσ_out S p q o (hN op' hop')
  · intro i
    exact congrFun (runOps_rename (rcbσ S p q o) N E
      (fun op hop => hA.inj (hN op hop))) i

/-! ## The end of the additions

`CachedJac.addEnd`, the code of `vg_<curve>_jac_add_tail`, which both
additions end with: from `U1`, `H`, `S1`, `r` in `t2`, `t3`, `t4`, `t5` and
`Z` in `o.z`, the sum `A` of `P` (at `p`) and the other point, for any `A`
that the values give: the double of `P` for `H = r = 0`, the point at
infinity for `H = 0` but not `r`, else the point `jacEndTail` computes. -/

/-- The values the end of the additions reads. -/
abbrev endIns (S : RcbSlots) (o : Pt) : List Nat := [S.t2, S.t3, S.t4, S.t5, o.z]

/-- `jacEndTail`: what it writes and the values it leaves. -/
theorem endTail_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2^(64*M.n))) {S : RcbSlots} {p q o : Pt}
    (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x)
    {W : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl W E s) (hW : ∀ x ∈ endIns S o, x ∈ W) :
    WP isa (ForwardField.programB M (jacEndTail S p q o)).inline s fun t =>
      ProgKeep M base (rcbW S o) s t ∧
      Inv M base size m Sl ([o.x,o.y,o.z] ++ W) (runOps (jacEndTail S p q o) E) t := by
  have hN : ∀ op ∈ jacEndTailN, op.out < 9 := by decide
  have hr : readsOk (jacEndTail S p q o) W = true := by
    rw [jacEndTail_eq S p q o]
    exact readsOk_mono (readsOk_rename (rcbσ S p q o)
      (show readsOk jacEndTailN [2,3,4,5,8] = true by decide)) (fun x hx => hW x hx)
  refine WP.mono (ForwardField.programB_ok hL hm _ hI
    (fun op hop x hx => hSl x (ofN_slots op (jacEndTail_eq S p q o ▸ hop) x hx)) hr)
    fun t ⟨kt,it⟩ => ⟨kt.mono ?_,it.sub ?_⟩
  · intro w hw
    obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hw
    rw [jacEndTail_eq S p q o] at hop
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hop
    rw [FOp.out_rename]
    exact rcbσ_out S p q o (hN n hn)
  · intro x hx
    rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · right
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [jacEndTail,jacTail,FOp.out]
    · exact Or.inl hx

/-- The end of the additions (`CachedJac.addEnd`): `o` represents any `A`
the values give, the double of `P` by `dbl`, the point at infinity, or the
sum `jacEndTail` computes. -/
theorem addEnd_ok {K : WinCfg} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl)
    (hm : UnitMod C.p (2^(64*K.M.n))) {dbl : RcbSlots → Pt → Pt → List FOp} (hd : JDblOk C dbl)
    {p q o : Pt} (hA : RcbApart K.S p q o)
    (hSl : ∀ x ∈ rcbW K.S o ++ rcbR K.S p q, Sl x)
    {W : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl W E s) (hW : ∀ x ∈ endIns K.S o, x ∈ W)
    (hpW : ∀ x ∈ rcbR K.S p p, x ∈ W)
    (hOne : K.one < C.p) {P A : Point C} (hP : onCurve C P = true)
    (hJP : InvJ C (E p.x) (E p.y) (E p.z) P)
    (hdbl : E K.S.t3 = 0 → E K.S.t5 = 0 → A = Spec.Weierstrass.add P P)
    (hinf : E K.S.t3 = 0 → E K.S.t5 ≠ 0 → A = .infinity)
    (hadd : E K.S.t3 ≠ 0 → InvJ C (runOps (jacEndTail K.S p q o) E o.x)
      (runOps (jacEndTail K.S p q o) E o.y) (runOps (jacEndTail K.S p q o) E o.z) A) :
    WP isa (CachedJac.addEnd K p q o dbl).inline s (JacPost K.M K.S base size C Sl W o A s) := by
  rw [CachedJac.addEnd]
  apply fieldBranch_ok hL hm hI (hW K.S.t3 (by simp))
  · intro d id kd hz
    apply fieldBranch_ok hL hm id (hW K.S.t5 (by simp))
    · intro e ie ke hrz
      have hdA : RcbApart K.S p p o := ⟨hA.nodup,fun x hx => hA.apart x (rcbR_self_mem _ _ _ hx)⟩
      have hdSl : ∀ x ∈ rcbW K.S o ++ rcbR K.S p p, Sl x := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hSl x (List.mem_append_left _ hx)
        · exact hSl x (List.mem_append_right _ (rcbR_self_mem _ _ _ hx))
      rw [hdbl hz hrz]
      refine WP.mono (jacDoubleForward_ok hL hm hd hdA hdSl ie hpW hP hJP) fun t ⟨kt,it,jt⟩ => ?_
      exact JacPost.prefix ⟨_,kt,it,jt⟩
        ((kd.mono (by regions_sub)).trans (ke.mono (by regions_sub)))
    · intro e ie ke hrz
      rw [hinf hz hrz]
      refine WP.mono (infinityPoint_ok hL
        (fun x hx => hSl x (by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
          rcases hx with rfl | rfl | rfl <;> simp [rcbW])) ie hOne) fun t ht => ?_
      exact JacPost.prefix ht ((kd.mono (by regions_sub)).trans (ke.mono (by regions_sub)))
  · intro d id kd hz
    refine WP.mono (endTail_ok hL hm hSl id hW) fun t ⟨kt,it⟩ => ?_
    exact JacPost.prefix ⟨_,kt,it,hadd hz⟩ (kd.mono (by regions_sub))

/-! ## The mixed addition -/

/-- The mixed header's three initial copies: `X1`, `Y1` and `Z1` to `t2`,
`t4` and `o.z`. -/
theorem jacMixedInitZ_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    {S : RcbSlots} {p q o : Pt} (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (.block (copy M.n S.t2 p.x ++ copy M.n S.t4 p.y ++ copy M.n o.z p.z)) s fun t =>
      ProgKeep M base (rcbW S o) s t ∧
      Inv M base size m Sl (o.z::S.t4::S.t2::V) (jacMixedInitZ S p o E) t := by
  rw [WP.block_append_iff]
  refine WP.mono (jacMixedInit_ok hL hSl hI hV) fun a ⟨ka,ia⟩ => ?_
  refine WP.mono (copyField_ok hL ia (hSl o.z (by simp [rcbW]))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hV p.z (by simp [rcbR]))))) fun t ⟨kt,it⟩ =>
    ⟨ka.trans (progKeep_of_op kt (by simp [rcbW])),it⟩

/-- The mixed header's field operations and its two exceptional-case values. -/
theorem jacMixedForwardHead_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2^(64*M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl (o.z::S.t4::S.t2::V) (jacMixedInitZ S p o E) s)
    (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (ForwardField.programB M (jacMixedHead S p q)).inline s fun t =>
      ProgKeep M base (rcbW S o) s t ∧
      Inv M base size m Sl (validAfter (jacMixedHead S p q) (o.z::S.t4::S.t2::V))
        (runOps (jacMixedHead S p q) (jacMixedInitZ S p o E)) t ∧
      runOps (jacMixedHead S p q) (jacMixedInitZ S p o E) S.t3 = E q.x*(E p.z*E p.z)-E p.x ∧
      runOps (jacMixedHead S p q) (jacMixedInitZ S p o E) S.t5 = E q.y*E p.z*(E p.z*E p.z)-E p.y := by
  rw [jacMixedHead_eq S p q o]
  have hr := readsOk_rename (rcbσ S p q o)
    (show readsOk jacMixedHeadN [8,4,2,9,10,11,12,13,14,15,16] = true by decide)
  have hr' : readsOk (ofN jacMixedHeadN S p q o) (o.z::S.t4::S.t2::V) = true :=
    readsOk_mono hr (by
      intro x hx
      change x ∈ o.z::S.t4::S.t2::rcbR S p q at hx
      simp only [List.mem_cons] at hx ⊢
      rcases hx with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (hV x h))))
  refine WP.mono (ofN_forward_partial_ok hL hm
    (show ∀ op ∈ jacMixedHeadN, op.out<9 by decide) hA hSl hI hr')
    fun t ⟨kt,it,he⟩ => ⟨kt,it,?_,?_⟩
  · have h := he 3
    rw [jacMixedInitZ_rename hA] at h
    exact h.trans (jacMixedHeadZN_run (fun i => E (rcbσ S p q o i))).1
  · have h := he 5
    rw [jacMixedInitZ_rename hA] at h
    exact h.trans (jacMixedHeadZN_run (fun i => E (rcbσ S p q o i))).2

/-- Read-only coordinates survive the three initialization copies and header. -/
theorem jacMixedHeadZ_readonly {F : Type _} [Lean.Grind.CommRing F]
    {S : RcbSlots} {p q o : Pt} (hA : RcbApart S p q o) (E : Nat → F)
    {x : Nat} (hx : x ∈ rcbR S p q) :
    runOps (jacMixedHead S p q) (jacMixedInitZ S p o E) x = E x := by
  have hn2 : x≠S.t2 := fun he => hA.apart x hx (by rw [he]; simp [rcbW])
  have hn4 : x≠S.t4 := fun he => hA.apart x hx (by rw [he]; simp [rcbW])
  have hnz : x≠o.z := fun he => hA.apart x hx (by rw [he]; simp [rcbW])
  rw [runOps_of_not_out]
  · simp only [jacMixedInitZ,jacMixedInit,Fun.update_of_ne hnz,Fun.update_of_ne hn2,
      Fun.update_of_ne hn4]
  · intro op hop he
    have ho : op.out ∈ rcbW S o := by
      rw [jacMixedHead_eq S p q o] at hop
      obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hop
      rw [FOp.out_rename]
      exact rcbσ_out S p q o ((show ∀ n ∈ jacMixedHeadN, n.out<9 by decide) n hn)
    exact hA.apart x hx (he ▸ ho)

/-- The mixed header and the end compute the Jacobian sum with `Z2 = 1`. -/
theorem jacMixedZ_run {F : Type _} [Lean.Grind.CommRing F] {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (E : Nat → F) :
    let r := runOps (jacEndTail S p q o) (runOps (jacMixedHead S p q) (jacMixedInitZ S p o E))
    (r o.x, r o.y, r o.z) = jacAddF (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) 1 := by
  dsimp only
  rw [← runOps_append, jacMixedHead_eq S p q o, jacEndTail_eq S p q o]
  have he : ofN jacMixedHeadN S p q o ++ ofN jacEndTailN S p q o = ofN (jacMixedHeadN ++ jacEndTailN) S p q o := by
    simp only [ofN, List.map_append]
  rw [he]
  have hren := runOps_rename (rcbσ S p q o) (jacMixedHeadN ++ jacEndTailN) (jacMixedInitZ S p o E)
    (fun op hop => hA.inj ((show ∀ n ∈ jacMixedHeadN ++ jacEndTailN, n.out<9 by decide) op hop))
  rw [jacMixedInitZ_rename hA] at hren
  exact (congr (congrArg Prod.mk (congrFun hren 6))
    (congr (congrArg Prod.mk (congrFun hren 7)) (congrFun hren 8))).trans
    (jacMixedZN_run (fun i => E (rcbσ S p q o i)))

theorem jacMixedForward_ok {K : WinCfg} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) {dbl : RcbSlots → Pt → Pt → List FOp} (hd : JDblOk C dbl)
    {p q o : Pt} (hA : RcbApart K.S p q o)
    (hSl : ∀ x ∈ rcbW K.S o ++ rcbR K.S p q, Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s) (hV : ∀ x ∈ rcbR K.S p q, x ∈ V)
    (hOne : K.one < C.p) {P Q : Point C} (hP : onCurve C P = true) (hQ : onCurve C Q = true)
    (hJP : InvJ C (E p.x) (E p.y) (E p.z) P) (hJQ : InvJ C (E q.x) (E q.y) (E q.z) Q) (hAff : E q.z=1) :
    WP isa (Jacobian.jacMixedForward K p q o dbl).inline s
      (JacPost K.M K.S base size C Sl V o (Spec.Weierstrass.add P Q) s) := by
  rw [Jacobian.jacMixedForward]
  apply fieldBranch_ok hL hm hI (hV p.z (by simp [rcbR]))
  · intro a ia ka hz
    have hp := (hJP.z_zero_iff hC).mp hz
    rw [hp]
    exact WP.mono (copyPointJ_ok hL hA hSl ia hV hJQ)
      (fun t ht => ht.prefix (ka.mono (by regions_sub)))
  · intro a ia ka hpz
    have hqz : E q.z ≠ 0 := by rw [hAff]; exact hC.one_ne_zero
    apply WP.seq
    refine WP.mono (jacMixedInitZ_ok hL hSl ia hV) fun b ⟨kb,ib⟩ => ?_
    apply WP.seq
    refine WP.mono (jacMixedForwardHead_ok hL hm hA hSl ib hV) fun c ⟨kc,ic,eh,er⟩ => ?_
    let EH := runOps (jacMixedHead K.S p q) (jacMixedInitZ K.S p o E)
    have hkeep := (ka.mono (W' := rcbW K.S o) (by simp)).trans (kb.trans kc)
    have hpkeep : ∀ x ∈ rcbR K.S p q, EH x = E x := fun x hx => jacMixedHeadZ_readonly hA E hx
    have jp : InvJ C (EH p.x) (EH p.y) (EH p.z) P := by
      rw [hpkeep _ (by simp [rcbR]),hpkeep _ (by simp [rcbR]),hpkeep _ (by simp [rcbR])]
      exact hJP
    have oldV : ∀ x ∈ V, x ∈ validAfter (jacMixedHead K.S p q) (o.z::K.S.t4::K.S.t2::V) :=
      fun x hx => (mem_validAfter _ _).mpr (Or.inl (by simp [hx]))
    have hW : ∀ x ∈ endIns K.S o, x ∈ validAfter (jacMixedHead K.S p q) (o.z::K.S.t4::K.S.t2::V) := by
      intro x hx
      rw [mem_validAfter]
      simp only [endIns,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [jacMixedHead,FOp.out]
    have hv : ∀ x ∈ rcbR K.S p p, x ∈ validAfter (jacMixedHead K.S p q) (o.z::K.S.t4::K.S.t2::V) :=
      fun x hx => oldV x (hV x (rcbR_self_mem _ _ _ hx))
    have hx0 : EH K.S.t3 = 0 → E q.x*(E p.z*E p.z)-E p.x*(E q.z*E q.z)=0 := fun hz => by
      simpa only [hAff,Lean.Grind.Semiring.mul_one] using eh.symm.trans hz
    have hy0 : EH K.S.t5 = 0 → E q.y*E p.z*(E p.z*E p.z)-E p.y*E q.z*(E q.z*E q.z)=0 := fun hz => by
      simpa only [hAff,Lean.Grind.Semiring.mul_one] using er.symm.trans hz
    refine (WP.mono (addEnd_ok hL hm hd hA hSl ic hW hv hOne hP jp ?_ ?_ ?_)
      fun t ht => (JacPost.sub ht oldV).prefix hkeep)
    · intro hz hrz
      rw [hJP.same hC hJQ hpz hqz (hx0 hz) (hy0 hrz)]
    · intro hz hrz
      have hy : E q.y*E p.z*(E p.z*E p.z)-E p.y*E q.z*(E q.z*E q.z)≠0 := by
        intro he
        apply hrz
        rw [er]
        simpa only [hAff,Lean.Grind.Semiring.mul_one] using he
      exact hJP.opposite hC hP hQ hJQ hpz hqz (hx0 hz) hy
    · intro hz
      have hh : E q.x*(E p.z*E p.z)-E p.x*(E q.z*E q.z)≠0 := by
        intro he
        apply hz
        rw [eh]
        simpa only [hAff,Lean.Grind.Semiring.mul_one] using he
      have jt := hJP.add_ne' hC hP hQ hJQ hpz hqz hh
      dsimp only at jt
      rw [hAff,←jacMixedZ_run hA E] at jt
      exact jt


end VG.Proof.Weierstrass.X86_64
