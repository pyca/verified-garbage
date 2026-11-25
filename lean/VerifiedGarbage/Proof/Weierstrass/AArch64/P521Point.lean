module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Point
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
public import VerifiedGarbage.Proof.Weierstrass.Jac
public import VerifiedGarbage.Proof.Weierstrass.JacMadd
import VerifiedGarbage.Proof.Mont.AArch64.P521
import VerifiedGarbage.Proof.Framework.Block

/-!
# P-521's straight-line field programs, on AArch64

`program_ok`: a program (`Impl/Weierstrass/AArch64/P521Point.lean`) does what
the field operations it stands for do (`flat`), and the doubling and the
mixed addition are those of `dblJF` and `maddJF`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.P521

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Weierstrass.AArch64.P521
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass

/-- The field operations of a program. -/
def flat (l : List Step) : List FOp := l.flatMap Step.ops

/-- A multiple of which power of two it is. -/
def stepOk : Step → Bool
  | .op _ => true
  | .shl k _ _ => k == 1 || k == 2 || k == 3

theorem runOps_append {F : Type _} [Lean.Grind.CommRing F] : ∀ (l r : List FOp) (e : Nat → F),
    runOps (l ++ r) e = runOps r (runOps l e)
  | [], _, _ => rfl
  | op :: l, r, e => by rw [List.cons_append, runOps_cons, runOps_cons, runOps_append l r]

theorem readsOk_append : ∀ (l r : List FOp) (V : List Nat),
    readsOk (l ++ r) V = (readsOk l V && readsOk r (validAfter l V))
  | [], _, _ => by simp [readsOk, validAfter]
  | op :: l, r, V => by simp only [List.cons_append, readsOk, validAfter, readsOk_append l r, Bool.and_assoc]

private theorem keep_of_op {M : Mod} {base : Addr} {o : Nat} {W : List Nat} {s t : State} (h : OpKeep M base o s t)
    (ho : o ∈ W) : ProgKeep M base W s t :=
  ⟨h.gpr, h.rd, h.wr, h.sp, fun x hx ht => h.mem x (hx o ho) ht⟩

theorem ProgKeep.trans {M : Mod} {base : Addr} {W : List Nat} {s t u : State} (h : ProgKeep M base W s t)
    (k : ProgKeep M base W t u) : ProgKeep M base W s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp,
    fun x hx ht => (k.mem x hx ht).trans (h.mem x hx ht)⟩

/-- Doublings of a number, as a multiple. -/
private theorem toM_shl {m R v k : Nat} [NeZero m] (hk : k = 1 ∨ k = 2 ∨ k = 3) (o a : Nat) (E : Nat → Fin m)
    (hv : toM m R v = E a) :
    Function.update E o (toM m R (2 ^ k * v % m)) = runOps (Step.ops (.shl k o a)) E := by
  have dbl : ∀ x, toM m R ((x + x) % m) = toM m R x + toM m R x := fun x => toM_add ..
  have e2 : ∀ x, 2 * x % m = (x % m + x % m) % m := fun x => by rw [Nat.two_mul, Nat.add_mod]
  have step : ∀ x, toM m R (2 * x % m) = toM m R (x % m) + toM m R (x % m) := fun x => by rw [e2, dbl]
  have one : toM m R (2 * v % m) = E a + E a := by rw [Nat.two_mul, dbl, hv]
  rcases hk with rfl | rfl | rfl
  · funext y
    simp only [Step.ops, List.replicate, Nat.sub_self, runOps_cons, runOps_nil, FOp.run, Nat.pow_one, one]
  · funext y
    have two : toM m R (4 * v % m) = (E a + E a) + (E a + E a) := by
      rw [show 4 * v = 2 * (2 * v) by omega_arith, step, one]
    simp only [Step.ops, List.replicate, Nat.reduceSub, runOps_cons, runOps_nil, FOp.run, Nat.reducePow, two,
      Function.update_apply]
    split <;> rfl
  · funext y
    have two : toM m R (4 * v % m) = (E a + E a) + (E a + E a) := by
      rw [show 4 * v = 2 * (2 * v) by omega_arith, step, one]
    have three : toM m R (8 * v % m) = ((E a + E a) + (E a + E a)) + ((E a + E a) + (E a + E a)) := by
      rw [show 8 * v = 2 * (4 * v) by omega_arith, step, two]
    simp only [Step.ops, List.replicate, Nat.reduceSub, runOps_cons, runOps_nil, FOp.run, Nat.reducePow, three,
      Function.update_apply]
    split <;> rfl

theorem step_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hsp : supported M = true)
    (hL : Lay M size Sl) (hAl : Aligned M Sl) (hm : UnitMod m (2 ^ (64 * M.n))) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {st : Step} (hok : stepOk st = true) (hS : ∀ op ∈ st.ops, ∀ x ∈ op.out :: op.ins, Sl x)
    (hR : readsOk st.ops V = true) :
    WP isa (.block (st.code M)) s fun t => ProgKeep M base (st.ops.map FOp.out) s t ∧
      Inv M base size m Sl (validAfter st.ops V) (runOps st.ops E) t := by
  obtain ⟨hn, hp⟩ := P521.supported_mod hsp hI.mod.red
  cases st with
  | op f =>
    have hS' := hS f (List.mem_singleton_self f)
    have hR' : ∀ x ∈ f.ins, x ∈ V := by
      simp only [Step.ops, readsOk, Bool.and_true, List.all_eq_true, decide_eq_true_eq] at hR
      exact hR
    have fin : ∀ {t}, OpKeep M base f.out s t → Inv M base size m Sl (f.out :: V) (f.run E) t →
        ProgKeep M base ((Step.op f).ops.map FOp.out) s t ∧
          Inv M base size m Sl (validAfter (Step.op f).ops V) (runOps (Step.op f).ops E) t :=
      fun hk hi => ⟨keep_of_op hk (by simp [Step.ops]), hi⟩
    cases f with
    | mul o a b =>
      simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hS' hR'
      have hA := hI.lt a hR'.1
      have hB := hI.lt b hR'.2
      have ho := hL.le o hS'.1
      have ha := hL.le a hS'.2.1
      have hb := hL.le b hS'.2.2
      rw [hn] at ho ha hb
      rw [Step.code]
      have pk : ∀ {t}, OpKeepR 9 base o s t → wordsVal t.mem base o 9 < m →
          wordsVal t.mem base o 9 * 2 ^ (64 * 9) % m = wordsVal s.mem base a 9 * wordsVal s.mem base b 9 % m →
          ProgKeep M base ((Step.op (.mul o a b)).ops.map FOp.out) s t ∧
          Inv M base size m Sl (validAfter (Step.op (.mul o a b)).ops V) (runOps (Step.op (.mul o a b)).ops E) t := by
        intro t k hlt he
        have k' := Mont.AArch64.P521.toOpKeep hn k
        refine fin k' (hI.update hL hS'.1 k' (by rw [hn]; exact hlt) ?_)
        rw [← hn] at he
        rw [toM_mul hm he, hI.val a hR'.1, hI.val b hR'.2]
      rw [hn] at hA hB
      rw [hp] at hA hB
      split
      · rename_i hab
        obtain rfl := beq_iff_eq.mp hab
        exact WP.mono (Mont.AArch64.P521.sqrR_ok hI.scr.ptr hI.scr.ptrW (by decide) (by decide) ho ha (hAl.sl o hS'.1)
          (hAl.sl a hS'.2.1) hA) fun t ⟨k, h1, h2⟩ => pk k (by rw [hp]; exact h1) (by rw [hp]; exact h2)
      · exact WP.mono (Mont.AArch64.P521.mulR_ok hI.scr.ptr hI.scr.ptr hI.scr.ptrW (by decide) (by decide) (by decide) ho ha hb
          (hAl.sl o hS'.1) (hAl.sl a hS'.2.1) (hAl.sl b hS'.2.2) hA hB) fun t ⟨k, h1, h2⟩ => pk k (by rw [hp]; exact h1) (by rw [hp]; exact h2)
    | add o a b => exact WP.mono (fop_ok hL hAl hm hI hS' hR') fun t ⟨k, i⟩ => fin k i
    | sub o a b => exact WP.mono (fop_ok hL hAl hm hI hS' hR') fun t ⟨k, i⟩ => fin k i
  | shl k o a =>
    have hk : k = 1 ∨ k = 2 ∨ k = 3 := by
      simpa only [stepOk, Bool.or_eq_true, beq_iff_eq, or_assoc] using hok
    have hS' := hS (.add o a a) (List.mem_cons_self ..)
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hS'
    have hR' : a ∈ V := by
      simp only [Step.ops, readsOk, Bool.and_eq_true, FOp.ins, List.all_cons, decide_eq_true_eq] at hR
      exact hR.1.1
    have hA := hI.lt a hR'
    have ho := hL.le o hS'.1
    have ha := hL.le a hS'.2.1
    rw [hn] at ho ha hA
    rw [hp] at hA
    refine WP.mono (Mont.AArch64.P521.shl_ok hI.scr hk ho ha (hAl.sl o hS'.1) (hAl.sl a hS'.2.1) hA) fun t ⟨kk, he⟩ => ?_
    have k' := Mont.AArch64.P521.toOpKeep hn kk
    refine ⟨keep_of_op k' (by simp [Step.ops, FOp.out]), ?_⟩
    rw [← hn, ← hp] at he
    have hI' := hI.update hL hS'.1 k' (by rw [he]; exact Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) (hI.lt a hR'))) rfl
    rw [he, toM_shl hk o a E (hI.val a hR')] at hI'
    refine hI'.sub fun x hx => ?_
    rw [mem_validAfter] at hx
    rcases hx with hx | hx
    · exact List.mem_cons_of_mem _ hx
    · obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hx
      rcases List.mem_cons.mp hop with rfl | hop
      · exact List.mem_cons_self ..
      · rw [(List.mem_replicate.mp hop).2]; exact List.mem_cons_self ..

theorem program_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hsp : supported M = true)
    (hL : Lay M size Sl) (hAl : Aligned M Sl) (hm : UnitMod m (2 ^ (64 * M.n))) :
    ∀ (l : List Step) {V : List Nat} {E : Nat → Fin m} {s : State}, Inv M base size m Sl V E s →
      (∀ st ∈ l, stepOk st = true) → (∀ op ∈ flat l, ∀ x ∈ op.out :: op.ins, Sl x) → readsOk (flat l) V = true →
      WP isa (program M l) s fun t => ProgKeep M base ((flat l).map FOp.out) s t ∧
        Inv M base size m Sl (validAfter (flat l) V) (runOps (flat l) E) t
  | [], _, _, s, hI, _, _, _ => WP.block_nil ⟨ProgKeep.refl _ _ _ s, hI⟩
  | [st], V, E, s, hI, hok, hS, hR => by
    have e : flat [st] = st.ops := by simp [flat]
    rw [e] at hS hR ⊢
    exact step_ok hsp hL hAl hm hI (hok st (List.mem_cons_self ..)) hS hR
  | st :: st' :: l, V, E, s, hI, hok, hS, hR => by
    have e : flat (st :: st' :: l) = st.ops ++ flat (st' :: l) := by simp [flat]
    rw [e] at hS hR ⊢
    rw [readsOk_append, Bool.and_eq_true] at hR
    show WP isa (.seq (.block (st.code M)) (program M (st' :: l))) s _
    refine WP.seq (WP.mono (step_ok hsp hL hAl hm hI (hok st (List.mem_cons_self ..))
      (fun op h => hS op (List.mem_append_left _ h)) hR.1) fun u ⟨ku, iu⟩ => ?_)
    refine WP.mono (program_ok hsp hL hAl hm (st' :: l) iu (fun q h => hok q (List.mem_cons_of_mem _ h))
      (fun op h => hS op (List.mem_append_right _ h)) hR.2) fun t ⟨kt, it⟩ => ⟨?_, ?_⟩
    · rw [List.map_append]
      exact ProgKeep.trans (ku.mono fun w h => List.mem_append_left _ h) (kt.mono fun w h => List.mem_append_right _ h)
    · rw [runOps_append]
      refine it.sub fun x hx => ?_
      rw [mem_validAfter, List.map_append, List.mem_append] at hx
      rw [mem_validAfter, mem_validAfter]
      rcases hx with hx | hx | hx
      · exact .inl (.inl hx)
      · exact .inl (.inr hx)
      · exact .inr hx

/-! ## The doubling and the mixed addition -/

/-- The doubling's operations, on numbered slots. -/
def doubleN : List FOp := flat (doubleSteps ⟨9, 10, 0, 1, 2, 3, 4, 5⟩ ⟨11, 12, 13⟩ ⟨6, 7, 8⟩)

theorem doubleN_ok : NumOk doubleN := ⟨by decide, by decide, by decide⟩

theorem double_eq (S : RcbSlots) (p o : Pt) : flat (doubleSteps S p o) = ofN doubleN S p p o := rfl

theorem doubleSteps_ok (S : RcbSlots) (p o : Pt) : ∀ st ∈ doubleSteps S p o, stepOk st = true :=
  List.all_eq_true.mp (show (doubleSteps S p o).all stepOk = true from rfl)

theorem doubleN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    (runOps doubleN e 6, runOps doubleN e 7, runOps doubleN e 8) = dblJF (e 11) (e 12) (e 13) := by
  simp only [doubleN, flat, doubleSteps, List.flatMap_cons, List.flatMap_nil, Step.ops, List.replicate, Nat.reduceSub,
    List.cons_append, List.nil_append, runOps_cons, runOps_nil, FOp.run, Function.update_apply, dblJF, Prod.mk.injEq,
    Nat.reduceEqDiff, ite_true, ite_false]
  refine ⟨?_, ?_, ?_⟩ <;> grind

/-- The mixed addition's operations are the field program's. -/
theorem madd_eq (S : RcbSlots) (p q o : Pt) : flat (maddSteps S p q o) = maddJ S p q o := by
  simp [flat, maddSteps, maddJ, Step.ops]

theorem maddSteps_ok (S : RcbSlots) (p q o : Pt) : ∀ st ∈ maddSteps S p q o, stepOk st = true := by
  simp [maddSteps, maddJ, stepOk]

end VG.Proof.Weierstrass.AArch64.P521
