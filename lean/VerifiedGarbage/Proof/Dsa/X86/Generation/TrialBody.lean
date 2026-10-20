module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialState
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialEntry
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialStep
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Trial division stops at the first divisor or checks the complete table -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem trialCheckBody_ok {s : State} {base : Addr} {input table : BitVec 32} {len entries : Nat}
    (R : TrialInputs s base input table len entries) (si : s.gpr .esi = input) (di : s.gpr .edi = table) :
    WP isa (trialCheckBody len entries) s fun u => TrialContext s base u ∧
      u.gpr .eax = trialStatus entries (trialValue s input len) := by
  unfold trialCheckBody
  refine WP.seq (WP.mono (trialCheckEntry_ok (TrialContext.refl R.frame) si di)
    fun a ⟨Ca, src, tab, idx, status⟩ => ?_)
  have I : TrialLoopInv s base input table len 0 a := ⟨Ca, src, tab, idx, status, by omega⟩
  refine WP.seq (WP.mono (WP.loop (M := isa) (Q := TrialDone s base input len entries) (fun k t => ∃ i, k = entries - i ∧ i < entries ∧
    TrialLoopInv s base input table len i t) ?_ entries a ⟨0, rfl, R.entriesPos, I⟩) ?_)
  · rintro k t ⟨i, rfl, hi, I⟩
    refine WP.mono (trialCheckStep_ok R hi I) fun u ⟨_, h⟩ => ?_
    rcases h with ⟨zf, done⟩ | ⟨zf, more, next⟩
    · exact .inl ⟨by simp only [eval, zf, Option.map_some, Bool.not_true], done⟩
    · exact .inr ⟨by simp only [eval, zf, Option.map_some, Bool.not_false],
        entries - (i + 1), by omega, i + 1, rfl, more, next⟩
  · rintro t ⟨Ct, status⟩
    refine wp_movS (v := trialStatus entries (trialValue s input len))
      (by rw [Ct.frame.read (by decide), status]) fun u tu _ => WP.block_nil ?_
    exact ⟨Ct.upd tu (by decide), tu.gpr⟩
end VG.Proof.Dsa.X86.Generation
