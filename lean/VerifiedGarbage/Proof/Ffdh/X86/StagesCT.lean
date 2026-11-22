module

public import VerifiedGarbage.Proof.Ffdh.X86.Stages
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
public import VerifiedGarbage.Impl.Ffdh.X86.Domain
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
meta import VerifiedGarbage.Impl.Ffdh.X86.Domain
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
import VerifiedGarbage.Proof.Ffdh.X86.EntryCT
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeMul
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.X86.CallBody
import VerifiedGarbage.Proof.Framework.X86.RelCT

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

/-- The callee, from the copy of the arguments: `prepare_relCT`, on its states narrowed to the working space. -/
theorem callee_relCT :
    RelCT isa (Both (CalleeAt base bytes len args sp)) (prepare .wide) fun _ _ => True := by
  have run : ∀ u, CalleeAt base bytes len args sp u →
      Run (fun _ _ => True) base bytes len args (sp - BitVec.ofNat 32 80) (narrowed base bytes u) := fun u C =>
    ⟨VG.Proof.Ffdh.X86.In.narrow C.1 trivial, ⟨C.1.top, fun r hr => by rw [List.mem_singleton.mp hr]; exact C.2.2⟩, C.2.1⟩
  have cov : ∀ u, CalleeAt base bytes len args sp u →
      Covers ((u.rd ++ u.wr) ++ [⟨base, bytes⟩]) (u.rd ++ u.wr) ∧ Covers [⟨base, bytes⟩] u.wr := fun u C => by
    have c : Covers [⟨base, bytes⟩] u.wr :=
      Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact C.1.scratch.wr
    exact ⟨Covers.append_left (Covers.refl _) (Covers.right c), c⟩
  refine VG.Proof.Bignum.X86.PublicRt.relCT_narrow (fun u => u.rd ++ u.wr) (fun _ => [⟨base, bytes⟩])
    (fun f g ⟨C₁, C₂⟩ => ?_) ((prepare_relCT (Ex := fun _ _ => True) (base := base) (bytes := bytes) (len := len) (args := args)
      (sp := sp - BitVec.ofNat 32 80) .wide).mono
      (fun _ _ h => h) fun _ _ _ => trivial)
  exact ⟨(cov f C₁).1, (cov f C₁).2, (cov g C₂).1, (cov g C₂).2, ⟨_, prepCtx_ok (run f C₁).1 .wide⟩,
    ⟨_, prepCtx_ok (run g C₂).1 .wide⟩, run f C₁, run g C₂⟩

/-- The call of `prepare .wide`: the copy of the arguments checked by the taint analysis from `esp`, and the
callee by `callee_relCT`. -/
theorem prepCall_trace :
    RelCT isa (Both fun s => Run Ex base bytes len args sp s ∧ RoomF sp base bytes) Impl.Ffdh.X86.prepCall fun _ _ => True := by
  unfold Impl.Ffdh.X86.prepCall
  refine RelCT.callBody (R := fun a b => ∃ s₁ s₂,
      (Both fun s => Run Ex base bytes len args sp s ∧ RoomF sp base bytes) s₁ s₂ ∧
        a = s₁.callEntry ∧ b = s₂.callEntry) ?_ (fun s t h => ⟨s, t, h, rfl, rfl⟩)
    (fun _ _ h => h.1.1.2.2.trans h.2.1.2.2.symm)
  refine RelCT.frameAlloc (R := fun _ _ => True) (VG.RelCT.seq ?_ (callee_relCT (base := base) (bytes := bytes) (len := len) (args := args) (sp := sp)))
  refine ((RelCT.taint (A := taint) (τr [.esp]) (fun a b h => agree_regs fun r hr => ?_) (hc := .block [])
    (by rfl)).wp (F₁ := CalleeAt base bytes len args sp) (F₂ := CalleeAt base bytes len args sp)
      fun a b h => ?_).mono (fun _ _ h => h) fun _ _ h => h.2
  · obtain rfl := List.mem_singleton.mp hr
    obtain ⟨c₁, c₂, ⟨x₁, x₂, ⟨⟨R₁, -⟩, ⟨R₂, -⟩⟩, rfl, rfl⟩, rfl, rfl⟩ := h
    rw [allocFrame_esp, allocFrame_esp, State.callEntry_esp, State.callEntry_esp, R₁.2.2, R₂.2.2]
  · obtain ⟨c₁, c₂, ⟨x₁, x₂, ⟨⟨R₁, F₁⟩, ⟨R₂, F₂⟩⟩, rfl, rfl⟩, rfl, rfl⟩ := h
    obtain w : ∀ {x : State}, Run Ex base bytes len args sp x → RoomF sp base bytes →
        WP isa (.block ((List.range 18).flatMap Impl.Ffdh.X86.copyArg)) (allocFrame Impl.Ffdh.X86.argsFrame x.callEntry)
          (CalleeAt base bytes len args sp) := fun {x} R F => by
      have e := R.2.2
      rw [← e] at F ⊢
      exact callee_at R.1 F
    exact ⟨w R₁ F₁, w R₂ F₂⟩

/-- The context of p: the copy of p checked by the taint analysis, and its setup by `prepCall`. -/
theorem ctxP_relCT :
    RelCT isa (Both fun s => Run Ex base bytes len args sp s ∧ RoomF sp base bytes) Impl.Ffdh.X86.ctxP
      (Both (WSt Ex base bytes len args sp .wide [3, 4] 0)) := by
  refine VG.RelCT.seq (taint_both (P := fun s => Run Ex base bytes len args sp s ∧ RoomF sp base bytes)
    (F := fun s => Run Ex base bytes len args sp s ∧ RoomF sp base bytes)
    (fun _ _ R₁ R₂ => R₁.1.agree R₂.1) _ ctxP_check fun _ R =>
      WP.mono (copyDown_run (j := 9) (d := 0) (by decide) (by decide) (by decide) R.1) fun _ h => ⟨h, R.2⟩) ?_
  refine relCT_both prepCall_trace fun x ⟨R, F⟩ => ?_
  have e := R.2.2
  rw [← e] at F
  refine WP.mono (prepCall_ok R.1 F) fun u ⟨C, one, R2, _, K⟩ => ?_
  obtain hM := safeM_gt (sv x.mem base len .wide 0)
  refine ⟨_, C, fun j hj => ?_, fun _ h => absurd h (Nat.not_lt_zero _), R.2.1.keep K, (K.1 _ (by decide)).trans e⟩
  rcases List.mem_cons.mp hj with rfl | hj
  · rw [one]; exact hM
  · rw [List.mem_singleton.mp hj, R2]; exact Nat.mod_lt _ (by omega_arith)

/-- A power modulo p: the base in slot `b`, the exponent in slot `e`. -/
theorem powP_trace {b e : Nat} (hb9 : 9 ≤ b) (hb : b ≤ 17) (he9 : 9 ≤ e) (he : e ≤ 17)
    (hcb : ACheck (copy (.slot .wide b) (.slot .wide 5) (one .wide)))
    (hce : ACheck (copy (.slot .wide e) (.slot .wide 8) (one .wide))) :
    RelCT isa (Both fun s => Run Ex base bytes len args sp s ∧ RoomF sp base bytes) (Impl.Ffdh.X86.powP b e)
      (Both (Run Ex base bytes len args sp)) := by
  unfold Impl.Ffdh.X86.powP
  refine VG.RelCT.seq ctxP_relCT ?_
  refine VG.RelCT.seq (taint_both (fun _ _ W₁ W₂ => W₁.agree W₂) _ hcb fun _ W =>
    copyDown_wst hb9 hb (by decide) (by decide) (by decide) (by decide) W) ?_
  refine VG.RelCT.seq (taint_both (fun _ _ W₁ W₂ => W₁.agree W₂) _ hce fun _ W =>
    copyDown_wst he9 he (by decide) (by decide) (by decide) (by decide) W) ?_
  exact (windowPower_relCT (winChecks .wide)).mono (fun _ _ h => h) fun _ _ h => ⟨h.1.run, h.2.run⟩

end VG.Proof.Ffdh.X86
