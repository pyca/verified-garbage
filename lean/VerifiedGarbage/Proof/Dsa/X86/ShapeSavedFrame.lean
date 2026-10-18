module

public import VerifiedGarbage.Proof.Dsa.X86.ShapeOperands
public import VerifiedGarbage.Proof.Dsa.X86.SavedFrame

/-! # Shape checking preserves saved registers and memory outside scratch -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86

theorem shapeFrame_outside {base : Addr} {m m' : Mem}
    (O : Outs base shapeRanges m m') : Outside base 0 8248 m m' := by
  intro a ha
  apply O a
  intro pair hp
  simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · change ofs base a < 0 ∨ 0 + 7048 ≤ ofs base a
    omega
  · change ofs base a < 8240 ∨ 8240 + 8 ≤ ofs base a
    omega

theorem shapeFrame_saved {base : Addr} {m m' : Mem} {regs : Reg → BitVec 32}
    (O : Outs base shapeRanges m m') (S : Saved m (off base) regs Entry.savedRegisters) :
    Saved m' (off base) regs Entry.savedRegisters := by
  intro pair hp
  have B := saved_bounds hp
  have H := (shapeFrame_outside O).val32 (d := pair.2) (k := 1) (.inr (by omega)) (by omega)
  have V : m'.readW (off base pair.2) 32 = m.readW (off base pair.2) 32 := by
    apply BitVec.eq_of_toNat_eq
    simpa only [val32, w32, Nat.mul_zero, Nat.add_zero] using H
  exact V.trans (S pair hp)

theorem execution_outside {base : Addr} {s t : State} (E : Execution base s t) :
    StackOutside (s.gpr .esp) base VG.Impl.Dsa.Layout.usedBytes s.mem t.mem := by
  intro a ha hstack
  apply E.mem a ?_ (.inr hstack)
  intro pair hp
  simp only [runRanges, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · change ofs base a < 0 ∨ 0 + 7048 ≤ ofs base a
    change 15712 ≤ ofs base a at ha
    omega
  · change ofs base a < 8244 ∨ 8244 + 4 ≤ ofs base a
    change 15712 ≤ ofs base a at ha
    omega
  · change ofs base a < 14720 ∨ 14720 + (15712 - 14720) ≤ ofs base a
    change 15712 ≤ ofs base a at ha
    omega

end VG.Proof.Dsa.X86
