module

public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Mont.X86.PowerTiming

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
