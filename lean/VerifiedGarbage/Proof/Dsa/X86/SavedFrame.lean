module

public import VerifiedGarbage.Proof.Dsa.X86.EntrySave
public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Proof.Dsa.X86.Execution

/-! # Saved ABI registers survive arithmetic and signature release -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86

theorem saved_bounds {p : Reg × Nat} (hp : p ∈ Entry.savedRegisters) :
    8256 ≤ p.2 ∧ p.2 + 4 ≤ 8272 := by
  simp only [Entry.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> decide

theorem Execution.saved {s t : State} {base : Addr} {g : Reg → BitVec 32}
    (E : Execution base s t) (S : Saved s.mem (off base) g Entry.savedRegisters) :
    Saved t.mem (off base) g Entry.savedRegisters := by
  intro p hp
  have B := saved_bounds hp
  have H : val32 t.mem base p.2 1 = val32 s.mem base p.2 1 := by
    apply E.mem.val32
    · intro pair hr
      simp only [runRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · change p.2 + 4 ≤ 0 ∨ 7048 ≤ p.2; omega
      · change p.2 + 4 ≤ 8244 ∨ 8248 ≤ p.2; omega
      · change p.2 + 4 ≤ 14720 ∨ 15712 ≤ p.2; omega
    · change p.2 + 4 * 1 ≤ 15712; omega
  have V : t.mem.readW (off base p.2) 32 = s.mem.readW (off base p.2) 32 := by
    apply BitVec.eq_of_toNat_eq
    simpa only [val32, Nat.mul_zero, Nat.add_zero] using H
  exact V.trans (S p hp)

theorem OutputFrame.saved {base out : Addr} {prefixSize len size : Nat} {m m' : Mem} {g : Reg → BitVec 32}
    (F : OutputFrame base out prefixSize len m m')
    (A : Region.Disjoint ⟨base, size⟩ ⟨out, len⟩)
    (hpre : prefixSize ≤ 8256) (hs : 8272 ≤ size) (hbound : size ≤ 2 ^ 64)
    (S : Saved m (off base) g Entry.savedRegisters) : Saved m' (off base) g Entry.savedRegisters := by
  intro p hp
  have B := saved_bounds hp
  exact (F.scratch_word A (by omega) (by omega) hbound).trans (S p hp)

end VG.Proof.Dsa.X86
