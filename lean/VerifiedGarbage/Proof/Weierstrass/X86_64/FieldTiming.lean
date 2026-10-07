import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-! Public field environments recover branch agreement after loads from scratch. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64

abbrev FieldPair (M : Mod) (base : Addr) (size m : Nat) [NeZero m]
    (Sl : Nat → Prop) (V : List Nat) (E : Nat → Fin m) (s t : State) : Prop :=
  Inv M base size m Sl V E s ∧ Inv M base size m Sl V E t

theorem FieldPair.sub {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V W : List Nat} {E : Nat → Fin m} {s t : State}
    (h : FieldPair M base size m Sl V E s t) (hw : ∀ x∈W,x∈V) :
    FieldPair M base size m Sl W E s t := ⟨h.1.sub hw,h.2.sub hw⟩

abbrev ScratchCT (c : Prog isa) : Prop :=
  ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs [.rdi])) c

theorem fieldPair_public {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m} {s t : State}
    (h : FieldPair M base size m Sl V E s t) :
    X86_64.Taint.Agree (Taint.ofRegs [.rdi]) s t := by
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h.1.scr.rdi.trans h.2.scr.rdi.symm

theorem scratch_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m} {c : Prog isa}
    (hc : ScratchCT c) :
    RelCT isa (FieldPair M base size m Sl V E) c (fun _ _ => True) :=
  fun _ _ _ _ _ _ hp es et => ⟨hc _ _ _ _ _ _ trivial trivial (fieldPair_public hp) es et,trivial⟩

theorem fieldProgram_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V W : List Nat} {E F : Nat → Fin m} {c : Prog isa}
    (hc : ScratchCT c)
    (hw : ∀ s, Inv M base size m Sl V E s → WP isa c s (Inv M base size m Sl W F)) :
    RelCT isa (FieldPair M base size m Sl V E) c (FieldPair M base size m Sl W F) :=
  ((scratch_relCT hc).wp (fun s t h => ⟨hw s h.1,hw t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

theorem fieldBranch_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hm : UnitMod m (2^(64*M.n)))
    {V : List Nat} {E : Nat → Fin m} {a : Nat} (ha : a∈V)
    (hc : ScratchCT (.block (Jacobian.zeroTest M.n a)))
    {yes no : Prog isa} {Q : State → State → Prop}
    (hy : E a=0 → RelCT isa (FieldPair M base size m Sl V E) yes Q)
    (hn : E a≠0 → RelCT isa (FieldPair M base size m Sl V E) no Q) :
    RelCT isa (FieldPair M base size m Sl V E)
      (.seq (.block (Jacobian.zeroTest M.n a)) (.ite .e yes no)) Q := by
  have hz := (scratch_relCT hc).wp (fun s t (h : FieldPair M base size m Sl V E s t) =>
    ⟨WP.mono (zeroField_ok hL hm h.1 ha) (fun _ ht => And.intro ht.1 ht.2.1),
     WP.mono (zeroField_ok hL hm h.2 ha) (fun _ ht => And.intro ht.1 ht.2.1)⟩)
  apply RelCT.seq hz
  apply RelCT.ite
  · intro s t h
    exact h.2.1.1.trans h.2.2.1.symm
  · intro s t ts tt s' t' ⟨h,he⟩ es et
    have he' : E a=0 := of_decide_eq_true (Option.some.inj (h.2.1.1.symm.trans he))
    exact hy he' _ _ _ _ _ _ ⟨h.2.1.2,h.2.2.2⟩ es et
  · intro s t ts tt s' t' ⟨h,he⟩ es et
    have he' : E a≠0 := of_decide_eq_false (Option.some.inj (h.2.1.1.symm.trans he))
    exact hn he' _ _ _ _ _ _ ⟨h.2.1.2,h.2.2.2⟩ es et

end VG.Proof.Weierstrass.X86_64
