import VerifiedGarbage.Impl.Weierstrass.AArch64.Jacobian
import VerifiedGarbage.Proof.Weierstrass.JacAdd
import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowDouble

/-! Jacobian addition field programs, including the header's public branch values. -/
namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64
open VG.Impl.Weierstrass VG.Proof.Mont.AArch64 VG.Proof.Mont

open Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem Inv.of_keeps {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m} {s t : State} {rs : List Reg}
    (h : Inv M base size m Sl V E s) (hk : Keeps rs s t) (h0 : Reg.x0 ∉ rs) :
    Inv M base size m Sl V E t :=
  ⟨h.scr.of_keeps hk h0,hk.mem ▸ h.mod,h.sl,hk.mem ▸ h.lt,hk.mem ▸ h.val⟩

/-- Testing a canonical field element tests its mathematical value, without
changing the environment or memory. -/
theorem zeroField_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod m (2 ^ (64 * M.n))) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {a : Nat} (ha : a ∈ V) :
    WP isa (.block (zeroMask M.n a)) s fun t =>
      t.gpr .x2 = mask (E a = 0) ∧ Inv M base size m Sl V E t ∧
      ProgKeep M base [] s t := by
  refine WP.mono (zeroMask_ok hI.scr hI.mod.n0 (hL.le a (hI.sl a ha))
    (hAl.sl a (hI.sl a ha))) fun t ⟨hv,hk⟩ => ⟨?_,hI.of_keeps hk (by decide),?_⟩
  · have hz := toM_eq_zero_iff hm (hI.lt a ha)
    rw [hI.val a ha] at hz
    rw [hv]
    simp only [mask, hz]
  · refine ⟨fun r hr => hk.gpr r ?_,hk.rd,hk.wr,hk.sp,fun _ _ _ => congrFun hk.mem _⟩
    intro he
    apply hr
    apply List.mem_append_left
    apply List.mem_append_left
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he ⊢
    rcases he with rfl | rfl | rfl | rfl | rfl <;> simp

/-- A field copy updates the same environment used by arithmetic operations. -/
theorem copyField_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {o a : Nat} (ho : Sl o) (ha : a ∈ V) :
    WP isa (.block (copy M.n o a)) s fun t =>
      OpKeep M base o s t ∧ Inv M base size m Sl (o :: V) (Function.update E o (E a)) t := by
  have hap : o ≤ a ∨ a + 8 * M.n ≤ o := by
    by_cases he : o = a
    · exact Or.inl (by omega)
    · have h := hL.apart o a ho (hI.sl a ha) he
      omega
  refine WP.mono (copy_ok M.n hI.scr (hL.le o ho) (hL.le a (hI.sl a ha))
    (hAl.sl o ho) (hAl.sl a (hI.sl a ha)) hap) fun t ⟨hv,hk,hO⟩ => ?_
  have hkeep : OpKeep M base o s t :=
    ⟨fun r hr => hk.gpr r (fun he => hr (by
        rw [List.mem_singleton] at he
        subst he
        simp [clob])),hk.rd,hk.wr,hk.sp,fun x hx _ => hO x hx⟩
  refine ⟨hkeep,hI.update hL ho hkeep ?_ ?_⟩
  · rw [hv]; exact hI.lt a ha
  · rw [hv]; exact hI.val a ha

/-- Setting a canonical field constant also uses the arithmetic environment. -/
theorem setField_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {o v : Nat} (ho : Sl o) (hv : v < m)
    (hR : m < 2 ^ (64 * M.n)) :
    WP isa (.block (setConst M.n o v)) s fun t =>
      OpKeep M base o s t ∧ Inv M base size m Sl (o :: V)
        (Function.update E o (toM m (2 ^ (64 * M.n)) v)) t := by
  refine WP.mono (setConst_ok hI.scr (hL.le o ho) (hAl.sl o ho) (Nat.lt_trans hv hR))
    fun t ⟨he,hk,hO⟩ => ?_
  have hkeep : OpKeep M base o s t :=
    ⟨fun r hr => hk.gpr r (fun he => hr (by
        rw [List.mem_singleton] at he
        subst he
        simp [clob])),hk.rd,hk.wr,hk.sp,fun x hx _ => hO x hx⟩
  refine ⟨hkeep,hI.update hL ho hkeep ?_ ?_⟩
  · rw [he]; exact hv
  · rw [he]

theorem ProgKeep.trans {M : Mod} {base : Addr} {W : List Nat} {s t u : State}
    (h1 : ProgKeep M base W s t) (h2 : ProgKeep M base W t u) : ProgKeep M base W s u :=
  ⟨fun r hr => (h2.gpr r hr).trans (h1.gpr r hr),h2.rd.trans h1.rd,
    h2.wr.trans h1.wr,h2.sp.trans h1.sp,fun x hx ht => (h2.mem x hx ht).trans (h1.mem x hx ht)⟩

theorem progKeep_of_op {M : Mod} {base : Addr} {W : List Nat} {o : Nat} {s t : State}
    (h : OpKeep M base o s t) (ho : o ∈ W) : ProgKeep M base W s t :=
  ⟨h.gpr,h.rd,h.wr,h.sp,fun x hx ht => h.mem x (hx o ho) ht⟩

/-- Copying a point retains its coordinates and the field environment. -/
theorem copyPoint_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    {S : RcbSlots} {p q o : Pt} (hA : RcbApart S p q o)
    (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (.block (copyPt M.n o q)) s fun t =>
      ∃ E', ProgKeep M base (rcbW S o) s t ∧
      Inv M base size m Sl ([o.x,o.y,o.z] ++ V) E' t ∧
      (E' o.x,E' o.y,E' o.z) = (E q.x,E q.y,E q.z) := by
  have hn : [o.x,o.y,o.z].Nodup := hA.nodup.drop (i := 6)
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,
    or_false,not_or,List.nodup_nil,and_true] at hn
  have hqa : ∀ x ∈ [q.x,q.y,q.z], ∀ y ∈ [o.x,o.y,o.z], x ≠ y := by
    intro x hx y hy he
    have hro : x ∈ rcbR S p q := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [rcbR]
    apply hA.apart x hro
    rw [he]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl <;> simp [rcbW]
  have hox : Sl o.x := hSl o.x (by simp [rcbW])
  have hoy : Sl o.y := hSl o.y (by simp [rcbW])
  have hoz : Sl o.z := hSl o.z (by simp [rcbW])
  have hqx := hV q.x (by simp [rcbR])
  have hqy := hV q.y (by simp [rcbR])
  have hqz := hV q.z (by simp [rcbR])
  rw [copyPt,List.append_assoc,WP.block_append_iff]
  refine WP.mono (copyField_ok hL hAl hI hox hqx) fun a ⟨ka,ia⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyField_ok hL hAl ia hoy (List.mem_cons_of_mem _ hqy)) fun b ⟨kb,ib⟩ => ?_
  refine WP.mono (copyField_ok hL hAl ib hoz
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hqz))) fun t ⟨kt,it⟩ => ?_
  refine ⟨_,(progKeep_of_op ka (by simp [rcbW])).trans
    ((progKeep_of_op kb (by simp [rcbW])).trans (progKeep_of_op kt (by simp [rcbW]))),
    it.sub ?_,?_⟩
  · intro x hx
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  · simp only [Function.update_self,Function.update_of_ne hn.1.1,
      Function.update_of_ne hn.1.2,Function.update_of_ne hn.2.1,
      Function.update_of_ne (hqa q.y (by simp) o.x (by simp)),
      Function.update_of_ne (hqa q.z (by simp) o.x (by simp)),
      Function.update_of_ne (hqa q.z (by simp) o.y (by simp))]

/-- The infinity branch writes a canonical nonzero y and zero z. -/
theorem infinityPoint_ok {K : WinCfg} {C : Spec.Weierstrass.Curve} {base : Addr} {size : Nat}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl)
    {o : Pt} (hSl : ∀ x ∈ [o.x,o.y,o.z], Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s) (hOne : K.one < C.p) :
    WP isa (.block (Jacobian.infinity K o)) s fun t =>
      ∃ E', ProgKeep K.M base (rcbW K.S o) s t ∧
      Inv K.M base size C.p Sl ([o.x,o.y,o.z] ++ V) E' t ∧
      InvJ C (E' o.x) (E' o.y) (E' o.z) .infinity := by
  have hR := wordsVal_lt s.mem base K.M.mo K.M.n
  rw [hI.mod.val] at hR
  have h0 : 0 < C.p := Nat.pos_of_ne_zero (NeZero.ne C.p)
  rw [Jacobian.infinity,List.append_assoc,WP.block_append_iff]
  refine WP.mono (setField_ok hL hAl hI (hSl o.x (by simp)) h0 hR) fun a ⟨ka,ia⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (setField_ok hL hAl ia (hSl o.y (by simp)) hOne hR) fun b ⟨kb,ib⟩ => ?_
  refine WP.mono (setField_ok hL hAl ib (hSl o.z (by simp)) h0 hR) fun t ⟨kt,it⟩ => ?_
  refine ⟨_,(progKeep_of_op ka (by simp [rcbW])).trans
    ((progKeep_of_op kb (by simp [rcbW])).trans (progKeep_of_op kt (by simp [rcbW]))),
    it.sub ?_,Or.inl ⟨rfl,?_⟩⟩
  · intro x hx
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  · rw [Function.update_self]
    simp only [toM, Fin.ofNat_zero, Lean.Grind.Semiring.zero_mul]

theorem eval_zero_mask {s : State} {P : Prop} [Decidable P]
    (h : s.gpr .x2 = mask P) : isa.eval (.nonzero .x .x2) s = some (decide P) := by
  change some (s.read .x .x2 != 0) = _
  rw [read_x,h]
  by_cases hp : P
  · simp only [mask,hp,ite_true,decide_true]; rfl
  · simp only [mask,hp,ite_false,decide_false]; rfl

/-- Branching on a canonical field element preserves the environment in both paths. -/
theorem fieldBranch_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod m (2 ^ (64 * M.n))) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {a : Nat} (ha : a ∈ V)
    {yes no : Prog isa} {Q : State → Prop}
    (hy : ∀ t, Inv M base size m Sl V E t → ProgKeep M base [] s t → E a = 0 → WP isa yes t Q)
    (hn : ∀ t, Inv M base size m Sl V E t → ProgKeep M base [] s t → E a ≠ 0 → WP isa no t Q) :
    WP isa (.seq (.block (zeroMask M.n a)) (.ite (.nonzero .x .x2) yes no)) s Q := by
  refine WP.seq (WP.mono (zeroField_ok hL hAl hm hI ha) fun t ⟨he,hi,hk⟩ => ?_)
  exact WP.ite (decide (E a = 0)) (eval_zero_mask he)
    (fun hz => hy t hi hk (of_decide_eq_true hz))
    (fun hz => hn t hi hk (of_decide_eq_false hz))

theorem _root_.VG.Proof.Weierstrass.RcbApart.swap {S : RcbSlots} {p q o : Pt} (h : RcbApart S p q o) :
    RcbApart S q p o := by
  refine ⟨h.nodup,fun x hx => h.apart x ?_⟩
  simp only [rcbR,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

theorem jacHead_readonly {F : Type _} [Lean.Grind.CommRing F]
    {S : RcbSlots} {p q o : Pt} (hA : RcbApart S p q o) (E : Nat → F)
    {x : Nat} (hx : x ∈ rcbR S p q) : runOps (jacHead S p q) E x = E x := by
  apply runOps_of_not_out
  intro op hop he
  have hmem : op ∈ ofN (jacHeadN ++ jacTailN) S p q o := by
    change op ∈ ofN jacHeadN S p q o ++ ofN jacTailN S p q o
    exact List.mem_append_left _ (jacHead_eq S p q o ▸ hop)
  exact hA.apart x hx (he ▸ ofN_out jacAddN_ok op hmem)

/-- A numbered program need not initialize all three output coordinates: the
addition header only initializes temporaries, before the exceptional-case branches. -/
theorem ofN_partial_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod m (2 ^ (64 * M.n))) {N : List FOp}
    (hN : ∀ op ∈ N, op.out < 9) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s)
    (hR : readsOk (ofN N S p q o) V = true) :
    WP isa (.block (fprog M (ofN N S p q o))) s fun s' =>
      ProgKeep M base (rcbW S o) s s' ∧
      Inv M base size m Sl (validAfter (ofN N S p q o) V)
        (runOps (ofN N S p q o) E) s' ∧
      ∀ i, runOps (ofN N S p q o) E (rcbσ S p q o i) =
        runOps N (fun j => E (rcbσ S p q o j)) i := by
  refine WP.mono (fprog_ok hL hAl hm _ hI
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

/-- The header computes the two public exceptional-case predicates in `t3`
and `t5`, while retaining the operands for the doubling or copying cases. -/
theorem jacHead_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod m (2 ^ (64 * M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (.block (fprog M (jacHead S p q))) s fun s' =>
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
  refine WP.mono (ofN_partial_ok hL hAl hm
    (show ∀ op ∈ jacHeadN, op.out < 9 by decide) hA hSl hI hr)
    fun s' ⟨hk,hi,he⟩ => ⟨hk,hi,?_,?_⟩
  · exact (he 3).trans (jacHeadN_run (fun j => E (rcbσ S p q o j))).2.1
  · exact (he 5).trans (jacHeadN_run (fun j => E (rcbσ S p q o j))).2.2.2

theorem readsOk_append (a b : List FOp) (V : List Nat) :
    readsOk (a ++ b) V = (readsOk a V && readsOk b (validAfter a V)) := by
  induction a generalizing V with
  | nil => rfl
  | cons op a ih =>
    simp only [List.cons_append, readsOk, validAfter, ih, Bool.and_assoc]

theorem runOps_append {F : Type _} [Lean.Grind.CommRing F]
    (a b : List FOp) (e : Nat → F) : runOps (a ++ b) e = runOps b (runOps a e) :=
  List.foldl_append

/-- Once the nonzero-H branch has been selected, the tail completes the
addition from the header's environment. -/
theorem jacTail_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod m (2 ^ (64 * M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl (validAfter (jacHead S p q) V)
      (runOps (jacHead S p q) E) s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (.block (fprog M (jacTail S p q o))) s fun s' =>
      ProgKeep M base (rcbW S o) s s' ∧
      Inv M base size m Sl ([o.x,o.y,o.z] ++ V)
        (runOps (jacHead S p q ++ jacTail S p q o) E) s' ∧
      (runOps (jacHead S p q ++ jacTail S p q o) E o.x,
       runOps (jacHead S p q ++ jacTail S p q o) E o.y,
       runOps (jacHead S p q ++ jacTail S p q o) E o.z) =
        jacAddF (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) (E q.z) := by
  have he : jacHead S p q ++ jacTail S p q o = ofN (jacHeadN ++ jacTailN) S p q o := by
    rw [jacHead_eq S p q o,jacTail_eq]
    simp only [ofN,List.map_append]
  have hr := readsOk_mono (ofN_readsOk jacAddN_ok S p q o) hV
  rw [← he,readsOk_append,Bool.and_eq_true] at hr
  have hw : ∀ op ∈ jacTail S p q o, op.out ∈ rcbW S o := by
    intro op hop
    exact ofN_out jacAddN_ok op (he ▸ List.mem_append_right _ hop)
  have hv : ∀ x ∈ [o.x,o.y,o.z], x ∈ (jacTail S p q o).map FOp.out := by
    simp only [jacTail,List.map_cons,List.map_nil,FOp.out,List.mem_cons,List.not_mem_nil,or_false]
    intro x hx
    rcases hx with rfl | rfl | rfl <;> simp
  refine WP.mono (fprog_ok hL hAl hm _ hI
    (fun op hop x hx => hSl x (ofN_slots op (he ▸ List.mem_append_right _ hop) x hx)) hr.2)
    fun s' ⟨hk,hi⟩ => ⟨hk.mono ?_,?_,?_⟩
  · intro w hw'
    obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hw'
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

/-- A point operation's frame, canonical field values, and represented point. -/
def JacPost (M : Mod) (S : RcbSlots) (base : Addr) (size : Nat) (C : Curve)
    (Sl : Nat → Prop) (V : List Nat) (o : Pt) (P : Point C) (s t : State) : Prop :=
  ∃ E, ProgKeep M base (rcbW S o) s t ∧ Inv M base size C.p Sl ([o.x,o.y,o.z]++V) E t ∧
    InvJ C (E o.x) (E o.y) (E o.z) P

theorem JacPost.prefix {M : Mod} {S : RcbSlots} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} {V : List Nat} {o : Pt} {P : Point C} {s t u : State}
    (h : JacPost M S base size C Sl V o P t u) (hk : ProgKeep M base (rcbW S o) s t) :
    JacPost M S base size C Sl V o P s u := by
  obtain ⟨E,k,i,j⟩ := h
  exact ⟨E,hk.trans k,i,j⟩

theorem JacPost.sub {M : Mod} {S : RcbSlots} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} {V W : List Nat} {o : Pt} {P : Point C} {s t : State}
    (h : JacPost M S base size C Sl V o P s t) (hV : ∀ x ∈ W, x ∈ V) :
    JacPost M S base size C Sl W o P s t := by
  obtain ⟨E,k,i,j⟩ := h
  refine ⟨E,k,i.sub ?_,j⟩
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact List.mem_append_left _ hx
  · exact List.mem_append_right _ (hV x hx)

theorem copyPointJ_ok {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    {S : RcbSlots} {p q o : Pt} (hA : RcbApart S p q o)
    (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv M base size C.p Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V)
    {Q : Point C} (hJ : InvJ C (E q.x) (E q.y) (E q.z) Q) :
    WP isa (.block (copyPt M.n o q)) s (JacPost M S base size C Sl V o Q s) := by
  refine WP.mono (copyPoint_ok hL hAl hA hSl hI hV) fun t ⟨E',hk,hi,he⟩ => ⟨E',hk,hi,?_⟩
  simp only [Prod.mk.injEq] at he
  rw [he.1,he.2.1,he.2.2]
  exact hJ

theorem rcbR_swap_mem (S : RcbSlots) (p q : Pt) (x : Nat) :
    x ∈ rcbR S q p ↔ x ∈ rcbR S p q := by
  simp only [rcbR,List.mem_cons,List.not_mem_nil,or_false]
  grind

theorem rcbR_self_mem (S : RcbSlots) (p q : Pt) {x : Nat} (h : x ∈ rcbR S p p) :
    x ∈ rcbR S p q := by
  simp only [rcbR,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
  grind

/-- Complete Jacobian addition on public data, including all exceptional cases. -/
theorem jacAdd_ok {K : WinCfg} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    {p q o : Pt} (hA : RcbApart K.S p q o)
    (hSl : ∀ x ∈ rcbW K.S o ++ rcbR K.S p q, Sl x)
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
        rw [List.mem_append,rcbR_swap_mem] at hx
        exact hSl x (List.mem_append.mpr hx)
      have hv : ∀ x ∈ rcbR K.S q p, x ∈ V := fun x hx => hV x ((rcbR_swap_mem _ _ _ _).mp hx)
      have hadd : Spec.Weierstrass.add P Q = P := by rw [hq]; cases P <;> rfl
      rw [hadd]
      exact WP.mono (copyPointJ_ok hL hAl hA.swap hs ib hv hJP)
        (fun t ht => (ht.prefix (kb.mono (by simp))).prefix (ka.mono (by simp)))
    · intro b ib kb hqz
      apply WP.seq
      apply (fprogB_wp _ _).mpr
      refine WP.mono (jacHead_ok hL hAl hm hA hSl ib hV) fun c ⟨kc,ic,eh,er⟩ => ?_
      let EH := runOps (jacHead K.S p q) E
      have hkeep := (ka.mono (W' := rcbW K.S o) (by simp)).trans
        ((kb.mono (by simp)).trans kc)
      have hpkeep : ∀ x ∈ rcbR K.S p q, EH x = E x := fun x hx => jacHead_readonly hA E hx
      have jp : InvJ C (EH p.x) (EH p.y) (EH p.z) P := by
        rw [hpkeep _ (by simp [rcbR]),hpkeep _ (by simp [rcbR]),hpkeep _ (by simp [rcbR])]
        exact hJP
      have oldV : ∀ x ∈ V, x ∈ validAfter (jacHead K.S p q) V :=
        fun x hx => (mem_validAfter _ _).mpr (Or.inl hx)
      have hv : ∀ x ∈ rcbR K.S p p, x ∈ validAfter (jacHead K.S p q) V :=
        fun x hx => oldV x (hV x (rcbR_self_mem _ _ _ hx))
      apply fieldBranch_ok hL hAl hm ic (a := K.S.t3) (by
        rw [mem_validAfter]; right; simp [jacHead,FOp.out])
      · intro d id kd hz
        have hx : E q.x*(E p.z*E p.z)-E p.x*(E q.z*E q.z)=0 := eh.symm.trans hz
        apply fieldBranch_ok hL hAl hm id (a := K.S.t5) (by
          rw [mem_validAfter]; right; simp [jacHead,FOp.out])
        · intro e ie ke hrz
          have hy : E q.y*E p.z*(E p.z*E p.z)-E p.y*E q.z*(E q.z*E q.z)=0 := er.symm.trans hrz
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
          have hy : E q.y*E p.z*(E p.z*E p.z)-E p.y*E q.z*(E q.z*E q.z)≠0 := fun he => hrz (er.trans he)
          have hadd := hJP.opposite hC hP hQ hJQ hpz hqz hx hy
          rw [hadd]
          refine WP.mono (infinityPoint_ok hL hAl
            (fun x hx => hSl x (by
              simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
              rcases hx with rfl | rfl | rfl <;> simp [rcbW])) ie hOne) fun t ht => ?_
          exact (JacPost.sub ht oldV).prefix
            (hkeep.trans ((kd.mono (by simp)).trans (ke.mono (by simp))))
      · intro d id kd hz
        have hh : E q.x*(E p.z*E p.z)-E p.x*(E q.z*E q.z)≠0 := fun he => hz (eh.trans he)
        apply (fprogB_wp _ _).mpr
        refine WP.mono (jacTail_ok hL hAl hm hA hSl id hV) fun t ⟨kt,it,ht⟩ => ?_
        have jt := hJP.add_ne hC ha hP hQ hJQ hpz hqz hh
        dsimp only at jt
        rw [←ht] at jt
        exact JacPost.prefix ⟨_,kt,it,jt⟩ (hkeep.trans (kd.mono (by simp)))

end VG.Proof.Weierstrass.AArch64
