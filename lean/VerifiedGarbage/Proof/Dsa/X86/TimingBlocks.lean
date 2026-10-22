module
public import VerifiedGarbage.Proof.Framework.X86.TaintErase
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Mont.X86.DynamicTiming

/-! # Composing byte-code timing checks while forgetting temporary registers -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86

theorem checkedProgramChange {τ σ τ' : VG.X86.Taint.T} {code : Prog isa} {hint : VG.Taint.Hint VG.X86.Taint.T}
    (H : VG.Taint.check taint τ code hint = some τ') (L : taint.le σ τ' = true) :
    RelCT isa (VG.X86.Taint.Agree τ) code (VG.X86.Taint.Agree σ) := by
  intro s t tr ur sf tf A E F
  obtain ⟨T, B⟩ := VG.Taint.check_sound H A E F
  exact ⟨T, taint.le_sound L B⟩

/-- A program whose code is `c₀`'s but for offsets and immediates, checked
on `c₀` (from a taint that knows no region base). -/
theorem erasedProgram_relCT {τ σ τ' : VG.X86.Taint.T} (c c₀ : Prog isa) (h : VG.Taint.Hint VG.X86.Taint.T)
    (e : Code.erase c = Code.erase c₀) (hn : VG.X86.Taint.noBases τ = true)
    (hh : VG.X86.Taint.hintNoBases h = true) (H : VG.Taint.check taint τ c₀ h = some τ')
    (L : taint.le σ τ' = true) :
    RelCT isa (VG.X86.Taint.Agree τ) c (VG.X86.Taint.Agree σ) :=
  checkedProgramChange ((VG.Proof.Mont.X86.Dynamic.check_of_erase_eq c c₀ τ h e hn hh).trans H) L

/-- `erasedProgram_relCT` with the check's result left to evaluation. -/
theorem erased_relCT {τ σ : VG.X86.Taint.T} (c c₀ : Prog isa) (h : VG.Taint.Hint VG.X86.Taint.T)
    (e : Code.erase c = Code.erase c₀) (hn : VG.X86.Taint.noBases τ = true)
    (hh : VG.X86.Taint.hintNoBases h = true)
    (L : (VG.Taint.check taint τ c₀ h).map (taint.le σ) = some true) :
    RelCT isa (VG.X86.Taint.Agree τ) c (VG.X86.Taint.Agree σ) := by
  obtain ⟨τ', H, L'⟩ := Option.map_eq_some_iff.mp L
  exact erasedProgram_relCT c c₀ h e hn hh H L'

theorem checkedBlockInvariant {τ τ' : VG.X86.Taint.T} {code : List Instr}
    (H : taint.checkBlock τ code = some τ') (L : taint.le τ τ' = true) :
    RelCT isa (VG.X86.Taint.Agree τ) (.block code) (VG.X86.Taint.Agree τ) := by
  intro s t tr ur sf tf A E F
  have C : VG.Taint.check taint τ (.block code) (.block []) = some τ' := H
  obtain ⟨T, B⟩ := VG.Taint.check_sound C A E F
  exact ⟨T, taint.le_sound L B⟩

theorem blockFlatMap_relCT {α : Type} (xs : List α) (code : α → List Instr)
    {P : State → State → Prop} (H : ∀ x, RelCT isa P (.block (code x)) P) :
    RelCT isa P (.block (xs.flatMap code)) P := by
  induction xs with
  | nil => exact RelCT.block_nil (fun _ _ h => h)
  | cons x xs ih =>
    rw [List.flatMap_cons]
    exact RelCT.block_append (RelCT.seq (H x) ih)


theorem wp_result {code : Prog isa} {s t : State} {trace : List Leak} {post : State → Prop}
    (W : WP isa code s post) (E : Exec isa code s trace t) : post t := by
  obtain ⟨_, u, F, P⟩ := W
  obtain ⟨_, rfl⟩ := Exec.det E F
  exact P

/-- A loop of `c` rounds, each related by `body`, its flag from each run's invariant. -/
theorem fixedLoop_relCT {body : Prog isa} {c : Nat}
    (I J : Nat → State → Prop) (positive : 0 < c)
    (rel : ∀ k, k < c → RelCT isa (fun s t => I k s ∧ J k t) body (fun _ _ => True))
    (left : ∀ k s, k < c → I k s → WP isa body s fun t =>
      I (k + 1) t ∧ t.zf = some (decide (c - (k + 1) = 0)))
    (right : ∀ k s, k < c → J k s → WP isa body s fun t =>
      J (k + 1) t ∧ t.zf = some (decide (c - (k + 1) = 0))) :
    RelCT isa (fun s t => I 0 s ∧ J 0 t) (.loop body .ne)
      (fun s t => I c s ∧ J c t) := by
  have loop := VG.RelCT.loop (M := isa) (body := body) (c := .ne)
    (Q := fun s t => I c s ∧ J c t)
    (fun remaining s t => ∃ k, k + remaining = c ∧ 0 < remaining ∧ I k s ∧ J k t)
    (fun remaining s t tr ur sf tf ⟨k, sum, pos, hs, ht⟩ es et => by
      have trace := (rel k (by omega) _ _ _ _ _ _ ⟨hs, ht⟩ es et).1
      obtain ⟨is, zs⟩ := VG.Proof.Dsa.X86.wp_result (left k s (by omega) hs) es
      obtain ⟨it, zt⟩ := VG.Proof.Dsa.X86.wp_result (right k t (by omega) ht) et
      refine ⟨trace, ?_, ?_, ?_⟩
      · change sf.zf.map (!·) = tf.zf.map (!·)
        rw [zs, zt]
      · intro done
        have last : k + 1 = c := by
          change sf.zf.map (!·) = some false at done
          rw [zs] at done
          simp only [Option.map_some, Option.some.injEq, Bool.not_eq_false', decide_eq_true_eq] at done
          omega
        exact ⟨last ▸ is, last ▸ it⟩
      · intro more
        have next : k + 1 < c := by
          change sf.zf.map (!·) = some true at more
          rw [zs] at more
          simp only [Option.map_some, Option.some.injEq, Bool.not_eq_true', decide_eq_false_iff_not] at more
          omega
        exact ⟨remaining - 1, by omega, k + 1, by omega, by omega, is, it⟩) c
  apply loop.mono
  · intro s t ⟨hs, ht⟩
    exact ⟨0, by omega, positive, hs, ht⟩
  · intro s t h; exact h

end VG.Proof.Dsa.X86
