module

public import VerifiedGarbage.Proof.Ffdh.X86.Stages
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
public import VerifiedGarbage.Impl.Ffdh.X86.Domain
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
meta import VerifiedGarbage.Impl.Ffdh.X86.Domain
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow

/-!
# FFDH on i686: the traces of the stages

Runs of the same stage from states with the same public values (`Both P`,
for a `P` that fixes them) leak the same traces: the stages without calls
are checked by the taint analysis from the arguments (`aRel`), a power
modulo p by private CRT's windowed power (`powP_trace`), and a branch on a
`Gate` whose condition `P` fixes takes the same side in both runs
(`gate_relCT`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both)

variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32}

/-- A run after a stage. -/
theorem run_step {s u : State} (R : Run Ex base bytes len args sp s) (S : Step Ex base bytes len args s u) :
    Run Ex base bytes len args sp u :=
  ⟨S.inp, R.2.1.keep S.keeps, S.esp.trans R.2.2⟩

/-- Code the taint analysis checks from the arguments, with what each run reaches. -/
theorem aRel {P F : State → Prop} {c : Prog isa} (hP : ∀ x, P x → Run Ex base bytes len args sp x)
    (hc : ACheck c) (hw : ∀ x, P x → WP isa c x F) : RelCT isa (Both P) c (Both F) :=
  relCT_both (RelCT.taint (A := taint) τA (fun _ _ h => (hP _ h.1).agree (hP _ h.2)) hc) hw

/-- Code whose runs from `Run` leak the same traces, with what each run reaches. -/
theorem runRel {P F : State → Prop} {c : Prog isa} (hP : ∀ x, P x → Run Ex base bytes len args sp x)
    (hct : RelCT isa (Both (Run Ex base bytes len args sp)) c fun _ _ => True) (hw : ∀ x, P x → WP isa c x F) :
    RelCT isa (Both P) c (Both F) :=
  relCT_both (hct.mono (fun _ _ h => ⟨hP _ h.1, hP _ h.2⟩) fun _ _ h => h) hw

/-- Code the taint analysis checks from the arguments, at the end. -/
theorem aEnd {P : State → Prop} {c : Prog isa} (hP : ∀ x, P x → Run Ex base bytes len args sp x)
    (hc : ACheck c) : RelCT isa (Both P) c fun _ _ => True :=
  RelCT.taint (A := taint) τA (fun _ _ h => (hP _ h.1).agree (hP _ h.2)) hc

/-- A branch on a gate the runs' `P` fixes. -/
theorem gate_relCT {P : State → Prop} {C : Prop} (hg : ∀ x, P x → Gate x C) {th el : Prog isa}
    {Q : State → State → Prop} (ht : RelCT isa (Both fun x => P x ∧ C) th Q)
    (he : RelCT isa (Both fun x => P x ∧ ¬ C) el Q) : RelCT isa (Both P) (.ite .e th el) Q := by
  refine VG.RelCT.ite (fun x y h => (hg _ h.1).agree (hg _ h.2)) (ht.mono (fun x y h => ?_) fun _ _ h => h)
    (he.mono (fun x y h => ?_) fun _ _ h => h)
  · obtain ⟨⟨P₁, P₂⟩, e⟩ := h
    obtain ⟨b, hb, i⟩ := hg _ P₁
    rw [hb] at e
    cases Option.some.inj e
    have c := i.mp rfl
    exact ⟨⟨P₁, c⟩, P₂, c⟩
  · obtain ⟨⟨P₁, P₂⟩, e⟩ := h
    obtain ⟨b, hb, i⟩ := hg _ P₁
    rw [hb] at e
    cases Option.some.inj e
    have c : ¬ C := fun c => by have := i.mpr c; cases this
    exact ⟨⟨P₁, c⟩, P₂, c⟩

theorem ctxP_check : ACheck (copy (.slot .wide 9) (.slot .wide 0) (one .wide)) := by
  dsimp only [ACheck]; taint_decide

/-- The context of p: the copy of p checked by the taint analysis, and its setup by `prepare_relCT`. -/
theorem ctxP_relCT :
    RelCT isa (Both (Run Ex base bytes len args sp)) Impl.Ffdh.X86.ctxP
      (Both (WSt Ex base bytes len args sp .wide [3, 4] 0)) :=
  VG.RelCT.seq (taint_both (fun _ _ R₁ R₂ => R₁.agree R₂) _ ctxP_check fun _ R =>
    copyDown_run (j := 9) (d := 0) (by decide) (by decide) (by decide) R) (prepare_relCT .wide)

/-- A power modulo p: the base in slot `b`, the exponent in slot `e`. -/
theorem powP_trace {b e : Nat} (hb9 : 9 ≤ b) (hb : b ≤ 17) (he9 : 9 ≤ e) (he : e ≤ 17)
    (hcb : ACheck (copy (.slot .wide b) (.slot .wide 5) (one .wide)))
    (hce : ACheck (copy (.slot .wide e) (.slot .wide 8) (one .wide))) :
    RelCT isa (Both (Run Ex base bytes len args sp)) (Impl.Ffdh.X86.powP b e) (Both (Run Ex base bytes len args sp)) := by
  unfold Impl.Ffdh.X86.powP
  refine VG.RelCT.seq ctxP_relCT ?_
  refine VG.RelCT.seq (taint_both (fun _ _ W₁ W₂ => W₁.agree W₂) _ hcb fun _ W =>
    copyDown_wst hb9 hb (by decide) (by decide) (by decide) (by decide) W) ?_
  refine VG.RelCT.seq (taint_both (fun _ _ W₁ W₂ => W₁.agree W₂) _ hce fun _ W =>
    copyDown_wst he9 he (by decide) (by decide) (by decide) (by decide) W) ?_
  exact (windowPower_relCT (winChecks .wide)).mono (fun _ _ h => h) fun _ _ h => ⟨h.1.run, h.2.run⟩

end VG.Proof.Ffdh.X86
