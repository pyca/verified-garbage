module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStore
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowState
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd

/-! Exact field equality through public in-scratch table transfers. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem FieldPair.rebuild {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V V' W : List Nat} {E Es Et : Nat → Fin m} {s t s' t' : State}
    (hL : Lay M size Sl) (hp : FieldPair M base size m Sl V E s t)
    (ks : ProgKeep M base W s s') (kt : ProgKeep M base W t t')
    (hW : ∀ x∈W, Sl x) (hi : Inv M base size m Sl V' Es s') (hj : Inv M base size m Sl V' Et t')
    (hv : ∀ x∈V', x∈W ∨ x∈V) (hn : ∀ x∈V', x∈W → Es x=Et x) :
    FieldPair M base size m Sl V' Es s' t' := by
  refine ⟨hi,hj.congr_env ?_,ks.sp.trans (hp.sp.trans kt.sp.symm)⟩
  intro x hx
  by_cases hw : x∈W
  · exact (hn x hx hw).symm
  · have hold := (hv x hx).resolve_left hw
    rw [←hj.val x hx,←hi.val x hx,kt.slot hL hp.right.scr hW (hj.sl x hx) hw,
      ks.slot hL hp.left.scr hW (hi.sl x hx) hw,hp.right.val x hold,hp.left.val x hold]

/-- A public transfer writes the same values in the same slots in both runs. -/
theorem fieldWrite_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) {V V' W : List Nat} {E F : Nat → Fin m}
    {c : Prog isa} {Pre : State → Prop} {rs : List Reg}
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs rs)) c)
    (hpub : ∀ s t, FieldPair M base size m Sl V E s t → Pre s → Pre t →
      AArch64.Taint.Agree (Taint.ofRegs rs) s t)
    (hW : ∀ x∈W, Sl x) (hV : ∀ x∈V', x∈W ∨ x∈V)
    (hw : ∀ s, Inv M base size m Sl V E s → Pre s → WP isa c s fun t =>
      ∃ E', ProgKeep M base W s t ∧ Inv M base size m Sl V' E' t ∧
        ∀ x∈V', x∈W → E' x=F x) :
    RelCT isa (fun s t => FieldPair M base size m Sl V E s t ∧ Pre s ∧ Pre t) c
      (fun s t => ∃ E', FieldPair M base size m Sl V' E' s t) := by
  intro s t ts tt s' t' ⟨hp,ps,pt⟩ es et
  obtain ⟨_,_,xs,Es,ks,is,vs⟩ := hw s hp.left ps
  obtain ⟨_,_,xt,Et,kt,it,vt⟩ := hw t hp.right pt
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  refine ⟨hct _ _ _ _ _ _ trivial trivial (hpub s t hp ps pt) es et,Es,?_⟩
  exact hp.rebuild hL ks kt hW is it hV (fun x hx hw => (vs x hx hw).trans (vt x hx hw).symm)

/-- Retain a known control register alongside a field relation. -/
theorem relCT_keepGpr {P Q : State → State → Prop} {c : Prog isa} {r : Reg} {v : BitVec 64}
    (h : RelCT isa P c Q) (hc : ∀ i∈instrs c, clobbers i r = false) (hr : r∉linkRegs) :
    RelCT isa (fun s t => P s t ∧ s.gpr r=v ∧ t.gpr r=v) c
      (fun s t => Q s t ∧ s.gpr r=v ∧ t.gpr r=v) := by
  intro s t ts tt s' t' ⟨hp,ps,pt⟩ es et
  obtain ⟨he,hq⟩ := h _ _ _ _ _ _ hp es et
  exact ⟨he,hq,(Exec.gpr hc es (Or.inr hr)).trans ps,(Exec.gpr hc et (Or.inr hr)).trans pt⟩

/-- Public control-register updates do not alter initialized field values. -/
theorem keepsField_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m} {c : Prog isa}
    {Pre Post : State → Prop} {pub rs : List Reg} (h0 : Reg.x0∉rs)
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs pub)) c)
    (hpub : ∀ s t, FieldPair M base size m Sl V E s t → Pre s → Pre t →
      AArch64.Taint.Agree (Taint.ofRegs pub) s t)
    (hw : ∀ s, Inv M base size m Sl V E s → Pre s →
      WP isa c s fun t => Post t ∧ Keeps rs s t) :
    RelCT isa (fun s t => FieldPair M base size m Sl V E s t ∧ Pre s ∧ Pre t) c
      (fun s t => FieldPair M base size m Sl V E s t ∧ Post s ∧ Post t) := by
  intro s t ts tt s' t' ⟨hp,ps,pt⟩ es et
  obtain ⟨_,_,xs,qs,ks⟩ := hw s hp.left ps
  obtain ⟨_,_,xt,qt,kt⟩ := hw t hp.right pt
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  exact ⟨hct _ _ _ _ _ _ trivial trivial (hpub s t hp ps pt) es et,
    ⟨hp.left.of_keeps ks h0,hp.right.of_keeps kt h0,ks.sp.trans (hp.sp.trans kt.sp.symm)⟩,qs,qt⟩

end VG.Proof.Weierstrass.AArch64
