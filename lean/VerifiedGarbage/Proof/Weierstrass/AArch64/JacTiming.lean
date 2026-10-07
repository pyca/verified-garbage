import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
Relational timing for arithmetic on public points. The two executions carry
one common field environment, so tests of exceptional coordinates agree even
though untouched scratch bytes and unrelated registers need not agree.
-/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

/-- Public initialized field slots, at a common scratch address and stack pointer. -/
structure FieldPair (M : Mod) (base : Addr) (size m : Nat) [NeZero m]
    (Sl : Nat → Prop) (V : List Nat) (E : Nat → Fin m) (s t : State) : Prop where
  left : Inv M base size m Sl V E s
  right : Inv M base size m Sl V E t
  sp : s.sp = t.sp

theorem FieldPair.public {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m} {s t : State}
    (h : FieldPair M base size m Sl V E s t) : AArch64.Taint.Agree (Taint.ofRegs [.x0]) s t := by
  refine ⟨h.sp,fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs,List.mem_singleton] at hr
  subst hr
  exact h.left.scr.x0.trans h.right.scr.x0.symm

/-- Exact field-program correctness keeps a public environment public. -/
theorem fprogB_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl) (hnc : Mont.callOf M = none)
    (hm : UnitMod m (2^(64*M.n))) (ops : List FOp)
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0])) (fprogB M ops))
    {V : List Nat} {E : Nat → Fin m}
    (hS : ∀ op ∈ ops, ∀ x ∈ op.out :: op.ins, Sl x) (hR : readsOk ops V = true) :
    RelCT isa (FieldPair M base size m Sl V E) (fprogB M ops)
      (FieldPair M base size m Sl (validAfter ops V) (runOps ops E)) := by
  intro s t ts tt s' t' hp es et
  have hs := (fprogB_wp M ops hnc).mpr (fprog_ok hL hAl hm ops hp.left hS hR)
  have ht := (fprogB_wp M ops hnc).mpr (fprog_ok hL hAl hm ops hp.right hS hR)
  obtain ⟨_,_,xs,ks,is⟩ := hs
  obtain ⟨_,_,xt,kt,it⟩ := ht
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  refine ⟨hct _ _ _ _ _ _ trivial trivial hp.public es et,is,it,
    ks.sp.trans (hp.sp.trans kt.sp.symm)⟩

/-- Branching on a public field element is safe; arbitrary unused scratch
contents never enter the equality premise. -/
theorem fieldBranch_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod m (2^(64*M.n))) {V : List Nat} {E : Nat → Fin m}
    {a : Nat} (ha : a ∈ V)
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0])) (.block (zeroMask M.n a)))
    {yes no : Prog isa} {Q : State → State → Prop}
    (hy : E a = 0 → RelCT isa (FieldPair M base size m Sl V E) yes Q)
    (hn : E a ≠ 0 → RelCT isa (FieldPair M base size m Sl V E) no Q) :
    RelCT isa (FieldPair M base size m Sl V E)
      (.seq (.block (zeroMask M.n a)) (.ite (.nonzero .x .x2) yes no)) Q := by
  intro s t ts tt s' t' hp es et
  cases es with
  | seq zs bs =>
    cases et with
    | seq zt bt =>
      obtain ⟨_,_,xs,vs,is,ks⟩ := zeroField_ok hL hAl hm hp.left ha
      obtain ⟨_,_,xt,vt,it,kt⟩ := zeroField_ok hL hAl hm hp.right ha
      obtain ⟨_,rfl⟩ := Exec.det zs xs
      obtain ⟨_,rfl⟩ := Exec.det zt xt
      have masks := (eval_zero_mask vs).trans (eval_zero_mask vt).symm
      have pair : FieldPair M base size m Sl V E _ _ :=
        ⟨is,it,ks.sp.trans (hp.sp.trans kt.sp.symm)⟩
      have hz := hct _ _ _ _ _ _ trivial trivial hp.public zs zt
      cases bs with
      | iteT cs bs =>
        cases bt with
        | iteT _ bt =>
          have he : E a = 0 := of_decide_eq_true (Option.some.inj ((eval_zero_mask vs).symm.trans cs))
          obtain ⟨hb,hq⟩ := hy he _ _ _ _ _ _ pair bs bt
          exact ⟨by rw [hz,hb],hq⟩
        | iteF ct _ => rw [masks,ct] at cs; cases cs
      | iteF cs bs =>
        cases bt with
        | iteT ct _ => rw [masks,ct] at cs; cases cs
        | iteF _ bt =>
          have he : E a ≠ 0 := of_decide_eq_false (Option.some.inj ((eval_zero_mask vs).symm.trans cs))
          obtain ⟨hb,hq⟩ := hn he _ _ _ _ _ _ pair bs bt
          exact ⟨by rw [hz,hb],hq⟩


/-- Any exact field-environment transition with fixed timing lifts to two runs. -/
theorem fieldWP_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V V' : List Nat} {E E' : Nat → Fin m} {c : Prog isa}
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0])) c)
    (hw : ∀ s, Inv M base size m Sl V E s →
      WP isa c s fun t => Inv M base size m Sl V' E' t ∧ t.sp = s.sp) :
    RelCT isa (FieldPair M base size m Sl V E) c (FieldPair M base size m Sl V' E') := by
  intro s t ts tt s' t' hp es et
  obtain ⟨_,_,xs,is,ks⟩ := hw s hp.left
  obtain ⟨_,_,xt,it,kt⟩ := hw t hp.right
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  exact ⟨hct _ _ _ _ _ _ trivial trivial hp.public es et,is,it,
    ks.trans (hp.sp.trans kt.symm)⟩

/-- Copying a public field slot preserves exact equality, including aliasing. -/
theorem copyField_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    {V : List Nat} {E : Nat → Fin m} {o a : Nat} (ho : Sl o) (ha : a ∈ V)
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0])) (.block (copy M.n o a))) :
    RelCT isa (FieldPair M base size m Sl V E) (.block (copy M.n o a))
      (FieldPair M base size m Sl (o :: V) (Function.update E o (E a))) := by
  apply fieldWP_relCT hct
  intro s hs
  exact WP.mono (copyField_ok hL hAl hs ho ha) fun _ ⟨hk,hi⟩ => ⟨hi,hk.sp⟩

/-- A fixed field constant supplies the same canonical value to both runs. -/
theorem setField_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    {V : List Nat} {E : Nat → Fin m} {o v : Nat} (ho : Sl o) (hv : v < m)
    (hR : m < 2^(64*M.n))
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0])) (.block (setConst M.n o v))) :
    RelCT isa (FieldPair M base size m Sl V E) (.block (setConst M.n o v))
      (FieldPair M base size m Sl (o :: V) (Function.update E o (toM m (2^(64*M.n)) v))) := by
  apply fieldWP_relCT hct
  intro s hs
  exact WP.mono (setField_ok hL hAl hs ho hv hR) fun _ ⟨hk,hi⟩ => ⟨hi,hk.sp⟩

/-- Only values in initialized slots are relevant to the relational invariant. -/
theorem Inv.congr_env {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V : List Nat} {E E' : Nat → Fin m} {s : State}
    (h : Inv M base size m Sl V E s) (he : ∀ x ∈ V, E x = E' x) :
    Inv M base size m Sl V E' s :=
  ⟨h.scr,h.mod,h.sl,h.lt,fun x hx => (h.val x hx).trans (he x hx)⟩

theorem FieldPair.sub {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V V' : List Nat} {E : Nat → Fin m} {s t : State}
    (h : FieldPair M base size m Sl V E s t) (hV : ∀ x ∈ V', x ∈ V) :
    FieldPair M base size m Sl V' E s t := ⟨h.left.sub hV,h.right.sub hV,h.sp⟩

end VG.Proof.Weierstrass.AArch64
