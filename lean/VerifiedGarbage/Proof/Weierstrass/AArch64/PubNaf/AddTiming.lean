module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Add
import VerifiedGarbage.Proof.Weierstrass.JacMul

/-!
# Timing of the additions and doublings whose products may be calls

Two runs from the same field values (`FieldPair`) leak the same trace and
end with the same values: `ofNB_relCT` (a numbered program whose products
may be calls), and `relCT_of_ct`, a piece of code constant time for some
public registers, from what each run satisfies.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

/-- A piece of code, constant time for the registers `G`, from two runs that
agree on them, and what each run satisfies. -/
theorem relCT_of_ct {P Q : State → State → Prop} {c : Prog isa} {G : List Reg}
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs G)) c)
    (hpub : ∀ s t, P s t → AArch64.Taint.Agree (Taint.ofRegs G) s t)
    (hw : ∀ s t, P s t → ∃ F₁ F₂ : State → Prop, WP isa c s F₁ ∧ WP isa c t F₂ ∧
      ∀ s' t', F₁ s' → F₂ t' → Q s' t') :
    RelCT isa P c Q := by
  intro s t ts tt s' t' hp es et
  obtain ⟨F₁, F₂, w₁, w₂, hq⟩ := hw s t hp
  obtain ⟨_, _, xs, fs⟩ := w₁
  obtain ⟨_, _, xt, ft⟩ := w₂
  obtain ⟨_, rfl⟩ := Exec.det es xs
  obtain ⟨_, rfl⟩ := Exec.det et xt
  exact ⟨hct _ _ _ _ _ _ trivial trivial (hpub s t hp) es et, hq _ _ fs ft⟩

/-- The timing of a numbered field program renamed to the formulas' slots (`ofN`), for products that may be calls. -/
theorem ofNB_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod m (2^(64*M.n))) {N : List FOp} (hN : NumOk N)
    {S : RcbSlots} {p q o : Pt} (hA : RcbApart S p q o)
    (hSl : ∀ x∈rcbW S o ++ rcbR S p q, Sl x) (hLow : Low M (rcbW S o ++ rcbR S p q))
    {V : List Nat} {E : Nat → Fin m} (hV : ∀ x∈rcbR S p q, x∈V)
    (hct : FieldCT (fprogB M (ofN N S p q o))) :
    RelCT isa (FieldPair M base size m Sl V E) (fprogB M (ofN N S p q o))
      (FieldPair M base size m Sl ([o.x,o.y,o.z]++V) (runOps (ofN N S p q o) E)) := by
  apply fieldWP_relCT hct
  intro s hi
  exact WP.mono (ofN_ok hL hAl hm hN hA hSl hLow hi hV) fun _ ⟨hk,it,_⟩ => ⟨it,hk.sp⟩

end VG.Proof.Weierstrass.AArch64
