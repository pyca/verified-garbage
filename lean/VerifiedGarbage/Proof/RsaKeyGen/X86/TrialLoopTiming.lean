module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialReadControl
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Trial
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Every divisor scans a fixed public number of candidate words -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.Trial

theorem wordStep_trace : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block (wordStep 4))
    (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl

theorem wordLoop_trace {g : Geometry} (v : g.Valid) :
    RelCT isa (fun s t => ReadControl g 0 s ∧ ReadControl g 0 t)
      (words 4) (VG.X86.Taint.Agree (τr [.esp, .edi])) := by
  unfold words
  refine (RelCT.loop (M := isa) (body := .block (wordStep 4)) (c := .ne)
    (I := fun q s t => ∃ j, q = 2 * g.w - j ∧ j < 2 * g.w ∧ ReadControl g j s ∧ ReadControl g j t)
    (Q := VG.X86.Taint.Agree (τr [.esp, .edi])) ?_ (2 * g.w)).mono
    (fun _ _ H => ⟨0, rfl, by have := v.positive; omega, H⟩) (fun _ _ H => H)
  rintro q s t tr ur u z ⟨j, rfl, index, S, T⟩ E G
  obtain ⟨trace, _⟩ := wordStep_trace _ _ _ _ _ _ (S.agree T) E G
  obtain ⟨U, Zu⟩ := wp_result (S.step v index) E
  obtain ⟨Z, Zz⟩ := wp_result (T.step v index) G
  have eu : isa.eval .ne u = some (!decide (j + 1 = 2 * g.w)) := by
    change u.zf.map Bool.not = _
    rw [Zu]
    rfl
  have ez : isa.eval .ne z = some (!decide (j + 1 = 2 * g.w)) := by
    change z.zf.map Bool.not = _
    rw [Zz]
    rfl
  refine ⟨trace, eu.trans ez.symm, fun _ => U.agree Z, ?_⟩
  intro next
  have more : j + 1 ≠ 2 * g.w := by
    intro done
    rw [eu, decide_eq_true done] at next
    cases next
  exact ⟨2 * g.w - (j + 1), by omega, j + 1, rfl, by omega, U, Z⟩

theorem finish_trace : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block finish)
    (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl

theorem divisor_trace {g : Geometry} (v : g.Valid) :
    RelCT isa (fun s t => ReadControl g 0 s ∧ ReadControl g 0 t)
      (divisor 4) (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  RelCT.seq (wordLoop_trace v) finish_trace

end VG.Proof.RsaKeyGen.X86.Sieve
