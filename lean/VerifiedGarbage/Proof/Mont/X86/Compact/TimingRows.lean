module

public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingRow
import VerifiedGarbage.Proof.Mont.X86.Compact.TimingLoad
import VerifiedGarbage.Proof.Mont.X86.Compact.TimingDigit
import VerifiedGarbage.Proof.Mont.X86.Compact.TimingControl

/-! # Prepared CIOS rows have the same trace for all secret operands -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem row_relCT {g : Geometry} (v : g.Valid) (i : Nat) (index : i < g.N) :
    RelCT isa (WindowPair g (g.S + Compact.accOff + 4 * i)) Compact.row
      (fun s t => WindowPair g (g.S + Compact.accOff + 4 * (i + 1)) s t ∧
        s.zf = some (decide (i + 1 = g.N)) ∧ t.zf = some (decide (i + 1 = g.N))) := by
  have acc : Compact.accOff = 24 := rfl
  unfold Compact.row
  exact RelCT.seq (loadA_positioned_relCT v i index)
    (RelCT.seq (mulRow_positioned_relCT v false _ (by omega) (by omega))
      (RelCT.seq (digit_relCT v _ (by omega))
        (RelCT.seq (mulRow_positioned_relCT v true _ (by omega) (by omega)) (rowEnd_relCT v i index))))

theorem rowLoop_relCT {g : Geometry} (v : g.Valid) :
    RelCT isa (WindowPair g (g.S + Compact.accOff)) (.loop Compact.row .ne)
      (WindowPair g (g.S + Compact.accOff + 4 * g.N)) := by
  let I : Nat → State → State → Prop := fun n s t =>
    ∃ i, n = g.N - i ∧ i < g.N ∧ WindowPair g (g.S + Compact.accOff + 4 * i) s t
  refine (RelCT.loop (Q := WindowPair g (g.S + Compact.accOff + 4 * g.N)) I ?_ g.N).mono
    (fun _ _ H => ⟨0, rfl, v.positive, by simpa only [Nat.mul_zero, Nat.add_zero] using H⟩) (fun _ _ H => H)
  intro n s t tr ur u z H E G
  obtain ⟨i, rfl, index, P⟩ := H
  obtain ⟨trace, W, Zu, Zz⟩ := row_relCT v i index _ _ _ _ _ _ P E G
  have eu : isa.eval .ne u = some (!decide (i + 1 = g.N)) := by
    change u.zf.map (!·) = _
    rw [Zu]; rfl
  have ez : isa.eval .ne z = some (!decide (i + 1 = g.N)) := by
    change z.zf.map (!·) = _
    rw [Zz]; rfl
  refine ⟨trace, eu.trans ez.symm, ?_, ?_⟩
  · intro exit
    rw [eu] at exit
    have done : i + 1 = g.N := by simpa using exit
    simpa only [done] using W
  · intro next
    rw [eu] at next
    have more : i + 1 ≠ g.N := by simpa using next
    exact ⟨g.N - (i + 1), by omega, i + 1, rfl, by omega, W⟩

end VG.Proof.Mont.X86.Compact
