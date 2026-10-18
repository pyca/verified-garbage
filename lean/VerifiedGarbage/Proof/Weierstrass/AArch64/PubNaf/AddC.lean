module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Add
public import VerifiedGarbage.Impl.Weierstrass.AArch64.PubNaf
import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-!
# Jacobian addition with the second point's cached `Z²` and `Z³`

`PubNaf.addC p q o` is `jacAdd` whose head reads `q`'s `Z²` and `Z³` from
`o.y` and `o.z`, which only the tail writes (`CachedJac.headAt`): on the
slots `rcbσ` numbers, `jacHeadCN` reads `7` and `8` (`jacAddCN_run`), and
`addCB_ok` is `jacAddB_ok` for it.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64
open VG.Impl.Weierstrass VG.Proof.Mont.AArch64 VG.Proof.Mont
open Spec.Weierstrass

/-- The cached head on numbered slots: `q.z`'s square and cube at `7` and `8`. -/
def jacHeadCN : List FOp := CachedJac.headAt ⟨9,10,0,1,2,3,4,5⟩ ⟨11,12,13⟩ ⟨14,15,16⟩ 7 8

theorem jacHeadC_eq (S : RcbSlots) (p q o : Pt) :
    CachedJac.headAt S p q o.y o.z = ofN jacHeadCN S p q o := rfl

theorem jacAddCN_out : ∀ op ∈ jacHeadCN ++ jacTailN, op.out < 9 := by decide
theorem jacHeadCN_out : ∀ op ∈ jacHeadCN, op.out < 9 := by decide
theorem jacAddCN_reads : readsOk (jacHeadCN ++ jacTailN) [7, 8, 9, 10, 11, 12, 13, 14, 15, 16] = true := by
  decide
theorem jacHeadCN_reads : readsOk jacHeadCN [7, 8, 9, 10, 11, 12, 13, 14, 15, 16] = true := by decide

section
variable {F : Type _} [Lean.Grind.CommRing F]

theorem jacHeadCN_run (e : Nat → F) (h7 : e 7 = e 16 * e 16) (h8 : e 8 = e 16 * (e 16 * e 16)) :
    runOps jacHeadCN e 3 = e 14 * (e 13 * e 13) - e 11 * (e 16 * e 16) ∧
    runOps jacHeadCN e 5 = e 15 * e 13 * (e 13 * e 13) - e 12 * e 16 * (e 16 * e 16) := by
  simp only [jacHeadCN, CachedJac.headAt, runOps, List.foldl_cons, List.foldl_nil, FOp.run,
    Function.update_apply]
  simp only [Nat.reduceEqDiff, ite_true, ite_false, h7, h8]
  constructor <;> grind

theorem jacAddCN_run (e : Nat → F) (h7 : e 7 = e 16 * e 16) (h8 : e 8 = e 16 * (e 16 * e 16)) :
    (runOps (jacHeadCN ++ jacTailN) e 6, runOps (jacHeadCN ++ jacTailN) e 7,
      runOps (jacHeadCN ++ jacTailN) e 8) = jacAddF (e 11) (e 12) (e 13) (e 14) (e 15) (e 16) := by
  simp only [jacHeadCN, jacTailN, CachedJac.headAt, jacTail, List.cons_append, List.nil_append, runOps,
    List.foldl_cons, List.foldl_nil, FOp.run, Function.update_apply]
  simp only [Nat.reduceEqDiff, ite_true, ite_false, h7, h8, jacAddF, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> grind

end

theorem jacHeadC_readonly {F : Type _} [Lean.Grind.CommRing F]
    {S : RcbSlots} {p q o : Pt} (hA : RcbApart S p q o) (E : Nat → F)
    {x : Nat} (hx : x ∈ rcbR S p q) : runOps (CachedJac.headAt S p q o.y o.z) E x = E x := by
  apply runOps_of_not_out
  intro op hop he
  rw [jacHeadC_eq, ofN, List.mem_map] at hop
  obtain ⟨op', h', rfl⟩ := hop
  rw [FOp.out_rename] at he
  exact hA.apart x hx (he ▸ rcbσ_out S p q o (jacHeadCN_out op' h'))

/-- The reads of the cached addition: `p`, `q`, the constants and `o.y`, `o.z`. -/
theorem readsC_sub {S : RcbSlots} {p q o : Pt} {V : List Nat} (hV : ∀ x ∈ rcbR S p q, x ∈ V)
    (hy : o.y ∈ V) (hz : o.z ∈ V) :
    ∀ x ∈ [7, 8, 9, 10, 11, 12, 13, 14, 15, 16].map (rcbσ S p q o), x ∈ V := by
  intro x hx
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hy
  · exact hz
  all_goals exact hV _ (by simp [rcbR, rcbσ, rcbW])

theorem jacHeadCB_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod m (2 ^ (64 * M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x)
    (hLow : Low M (rcbW S o ++ rcbR S p q))
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) (hy : o.y ∈ V) (hz : o.z ∈ V)
    (h2 : E o.y = E q.z * E q.z) (h3 : E o.z = E q.z * (E q.z * E q.z)) :
    WP isa (fprogB M (CachedJac.headAt S p q o.y o.z)) s fun s' =>
      ProgKeep M base (rcbW S o) s s' ∧
      Inv M base size m Sl (validAfter (CachedJac.headAt S p q o.y o.z) V)
        (runOps (CachedJac.headAt S p q o.y o.z) E) s' ∧
      runOps (CachedJac.headAt S p q o.y o.z) E S.t3 =
        E q.x * (E p.z * E p.z) - E p.x * (E q.z * E q.z) ∧
      runOps (CachedJac.headAt S p q o.y o.z) E S.t5 = E q.y * E p.z * (E p.z * E p.z) -
        E p.y * E q.z * (E q.z * E q.z) := by
  rw [jacHeadC_eq S p q o]
  have hr : readsOk (ofN jacHeadCN S p q o) V = true :=
    readsOk_mono (readsOk_rename (rcbσ S p q o) jacHeadCN_reads) (readsC_sub hV hy hz)
  refine WP.mono (ofN_partialB_ok hL hAl hm jacHeadCN_out hA hSl hLow hI hr)
    fun s' ⟨hk, hi, he⟩ => ⟨hk, hi, ?_, ?_⟩
  · exact (he 3).trans (jacHeadCN_run (fun j => E (rcbσ S p q o j)) h2 h3).1
  · exact (he 5).trans (jacHeadCN_run (fun j => E (rcbσ S p q o j)) h2 h3).2

theorem jacTailCB_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod m (2 ^ (64 * M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x)
    (hLow : Low M (rcbW S o ++ rcbR S p q))
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl (validAfter (CachedJac.headAt S p q o.y o.z) V)
      (runOps (CachedJac.headAt S p q o.y o.z) E) s) (hV : ∀ x ∈ rcbR S p q, x ∈ V)
    (hy : o.y ∈ V) (hz : o.z ∈ V)
    (h2 : E o.y = E q.z * E q.z) (h3 : E o.z = E q.z * (E q.z * E q.z)) :
    WP isa (fprogB M (jacTail S p q o)) s fun s' =>
      ProgKeep M base (rcbW S o) s s' ∧
      Inv M base size m Sl ([o.x,o.y,o.z] ++ V)
        (runOps (CachedJac.headAt S p q o.y o.z ++ jacTail S p q o) E) s' ∧
      (runOps (CachedJac.headAt S p q o.y o.z ++ jacTail S p q o) E o.x,
       runOps (CachedJac.headAt S p q o.y o.z ++ jacTail S p q o) E o.y,
       runOps (CachedJac.headAt S p q o.y o.z ++ jacTail S p q o) E o.z) =
        jacAddF (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) (E q.z) := by
  have he : CachedJac.headAt S p q o.y o.z ++ jacTail S p q o = ofN (jacHeadCN ++ jacTailN) S p q o := by
    rw [jacHeadC_eq S p q o, jacTail_eq]
    simp only [ofN, List.map_append]
  have hr : readsOk (ofN (jacHeadCN ++ jacTailN) S p q o) V = true :=
    readsOk_mono (readsOk_rename (rcbσ S p q o) jacAddCN_reads) (readsC_sub hV hy hz)
  rw [← he, readsOk_append, Bool.and_eq_true] at hr
  have hw : ∀ op ∈ jacTail S p q o, op.out ∈ rcbW S o := by
    intro op hop
    have hm' : op ∈ ofN (jacHeadN ++ jacTailN) S p q o := by
      change op ∈ ofN jacHeadN S p q o ++ ofN jacTailN S p q o
      exact List.mem_append_right _ (jacTail_eq S p q o ▸ hop)
    exact ofN_out jacAddN_ok op hm'
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
    have key := runOps_rename (rcbσ S p q o) (jacHeadCN ++ jacTailN) E
      fun op hop => hA.inj (jacAddCN_out op hop)
    exact (congrArg₂ Prod.mk (congrFun key 6) (congrArg₂ Prod.mk (congrFun key 7) (congrFun key 8))).trans
      (jacAddCN_run (fun i => E (rcbσ S p q o i)) h2 h3)

/-- `jacAddB_ok` for the cached addition: `q`'s `Z²` and `Z³` in `o.y` and `o.z`. -/
theorem addCB_ok {K : WinCfg} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl) (hn4 : K.M.n ≠ 4)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    {p q o : Pt} (hA : RcbApart K.S p q o)
    (hSl : ∀ x ∈ rcbW K.S o ++ rcbR K.S p q, Sl x) (hLow : Low K.M (rcbW K.S o ++ rcbR K.S p q))
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s) (hV : ∀ x ∈ rcbR K.S p q, x ∈ V)
    (hy : o.y ∈ V) (hz : o.z ∈ V)
    (h2 : E o.y = E q.z * E q.z) (h3 : E o.z = E q.z * (E q.z * E q.z))
    (hOne : K.one < C.p) {P Q : Point C} (hP : onCurve C P = true) (hQ : onCurve C Q = true)
    (hJP : InvJ C (E p.x) (E p.y) (E p.z) P) (hJQ : InvJ C (E q.x) (E q.y) (E q.z) Q) :
    WP isa (PubNaf.addC K p q o) s
      (JacPost K.M K.S base size C Sl V o (Spec.Weierstrass.add P Q) s) := by
  rw [PubNaf.addC]
  apply fieldBranch_ok hL hAl hm hI (hV p.z (by simp [rcbR]))
  · intro a ia ka hz'
    have hp := (hJP.z_zero_iff hC).mp hz'
    rw [hp]
    exact WP.mono (copyPointJ_ok hL hAl hA hSl ia hV hJQ)
      (fun t ht => ht.prefix (ka.mono (by simp)))
  · intro a ia ka hpz
    apply fieldBranch_ok hL hAl hm ia (hV q.z (by simp [rcbR]))
    · intro b ib kb hz'
      have hq := (hJQ.z_zero_iff hC).mp hz'
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
      refine WP.mono (jacHeadCB_ok hL hAl hm hA hSl hLow ib hV hy hz h2 h3)
        fun c ⟨kc, ic, eh, er⟩ => ?_
      let EH := runOps (CachedJac.headAt K.S p q o.y o.z) E
      have hkeep := (ka.mono (W' := rcbW K.S o) (by simp)).trans
        ((kb.mono (by simp)).trans kc)
      have hpkeep : ∀ x ∈ rcbR K.S p q, EH x = E x := fun x hx => jacHeadC_readonly hA E hx
      have jp : InvJ C (EH p.x) (EH p.y) (EH p.z) P := by
        rw [hpkeep _ (by simp [rcbR]), hpkeep _ (by simp [rcbR]), hpkeep _ (by simp [rcbR])]
        exact hJP
      have oldV : ∀ x ∈ V, x ∈ validAfter (CachedJac.headAt K.S p q o.y o.z) V :=
        fun x hx => (mem_validAfter _ _).mpr (Or.inl hx)
      have hv : ∀ x ∈ rcbR K.S p p, x ∈ validAfter (CachedJac.headAt K.S p q o.y o.z) V :=
        fun x hx => oldV x (hV x (rcbR_self_mem _ _ _ hx))
      apply fieldBranch_ok hL hAl hm ic (a := K.S.t3) (by
        rw [mem_validAfter]; right; simp [CachedJac.headAt, FOp.out])
      · intro d id kd hz'
        have hx : E q.x*(E p.z*E p.z)-E p.x*(E q.z*E q.z)=0 := eh.symm.trans hz'
        apply fieldBranch_ok hL hAl hm id (a := K.S.t5) (by
          rw [mem_validAfter]; right; simp [CachedJac.headAt, FOp.out])
        · intro e ie ke hrz
          have hy' : E q.y*E p.z*(E p.z*E p.z)-E p.y*E q.z*(E q.z*E q.z)=0 := er.symm.trans hrz
          have hpq := hJP.same hC hJQ hpz hqz hx hy'
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
          have hy' : E q.y*E p.z*(E p.z*E p.z)-E p.y*E q.z*(E q.z*E q.z)≠0 := fun he => hrz (er.trans he)
          have hadd := hJP.opposite hC hP hQ hJQ hpz hqz hx hy'
          rw [hadd]
          refine WP.mono (infinityPoint_ok hL hAl
            (fun x hx => hSl x (by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              rcases hx with rfl | rfl | rfl <;> simp [rcbW])) ie hOne) fun t ht => ?_
          exact (JacPost.sub ht oldV).prefix
            (hkeep.trans ((kd.mono (by simp)).trans (ke.mono (by simp))))
      · intro d id kd hz'
        have hh : E q.x*(E p.z*E p.z)-E p.x*(E q.z*E q.z)≠0 := fun he => hz' (eh.trans he)
        refine WP.mono (jacTailCB_ok hL hAl hm hA hSl hLow id hV hy hz h2 h3) fun t ⟨kt, it, ht⟩ => ?_
        have jt := hJP.add_ne hC ha hP hQ hJQ hpz hqz hh
        dsimp only at jt
        rw [← ht] at jt
        exact JacPost.prefix ⟨_, kt, it, jt⟩ (hkeep.trans (kd.mono (by simp)))

end VG.Proof.Weierstrass.AArch64
