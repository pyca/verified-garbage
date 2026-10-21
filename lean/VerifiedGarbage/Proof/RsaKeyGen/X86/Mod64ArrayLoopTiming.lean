module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Array
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayContext
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayStepTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayStep
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayLoadTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Candidate size alone controls the modular reduction's word loop -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem loop_trace {g : ArrayGeometry} (v : g.Valid) {candidate exponent other otherExponent : Nat} :
    RelCT isa (fun s t => ArrayState g candidate exponent 0 s ∧ ArrayState g other otherExponent 0 t)
      (.loop (arrayStep g.exponent) .ne) (VG.X86.Taint.Agree (τr [.esp, .edi])) := by
  refine (RelCT.loop (M := isa) (body := arrayStep g.exponent) (c := .ne)
    (I := fun q s t => ∃ i, i < g.n ∧ q = g.n - i ∧ ArrayState g candidate exponent i s ∧
      ArrayState g other otherExponent i t) (Q := VG.X86.Taint.Agree (τr [.esp, .edi])) ?_ g.n).mono
    (fun _ _ H => ⟨0, v.positive, rfl, H⟩) (fun _ _ H => H)
  rintro q s t tr ur u z ⟨i, index, rfl, S, T⟩ E G
  have trace := (arrayStep_trace _ _ _ _ _ _ ⟨S, T⟩ E G).1
  obtain ⟨U, Zu, _, _⟩ := wp_result (S.step v index) E
  obtain ⟨Z, Zz, _, _⟩ := wp_result (T.step v index) G
  have eu : isa.eval .ne u = some (!decide (i + 1 = g.n)) := by
    change u.zf.map Bool.not = _
    rw [Zu]
    rfl
  have ez : isa.eval .ne z = some (!decide (i + 1 = g.n)) := by
    change z.zf.map Bool.not = _
    rw [Zz]
    rfl
  refine ⟨trace, eu.trans ez.symm, fun _ => U.agree Z, ?_⟩
  intro next
  have more : i + 1 ≠ g.n := by
    intro done
    rw [eu, decide_eq_true done] at next
    cases next
  exact ⟨g.n - (i + 1), by omega, i + 1, by omega, rfl, U, Z⟩

end VG.Proof.RsaKeyGen.X86.Mod64
