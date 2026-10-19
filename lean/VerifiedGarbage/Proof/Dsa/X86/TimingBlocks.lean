module
public import VerifiedGarbage.Proof.Framework.X86.TaintErase
public import Mathlib.Tactic.Set
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

end VG.Proof.Dsa.X86
