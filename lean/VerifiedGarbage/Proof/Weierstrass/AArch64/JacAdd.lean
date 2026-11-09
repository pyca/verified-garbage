module

import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Production
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Jacobian
public import VerifiedGarbage.Proof.Weierstrass.JacAdd
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
public import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero
import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract

/-! Jacobian addition field programs, including the header's public branch values. -/

@[expose] public section

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

theorem readsOk_append (a b : List FOp) (V : List Nat) :
    readsOk (a ++ b) V = (readsOk a V && readsOk b (validAfter a V)) := by
  induction a generalizing V with
  | nil => rfl
  | cons op a ih =>
    simp only [List.cons_append, readsOk, validAfter, ih, Bool.and_assoc]

theorem runOps_append {F : Type _} [Lean.Grind.CommRing F]
    (a b : List FOp) (e : Nat → F) : runOps (a ++ b) e = runOps b (runOps a e) :=
  List.foldl_append

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

end VG.Proof.Weierstrass.AArch64
