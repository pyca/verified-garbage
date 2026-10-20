module

public import VerifiedGarbage.Impl.Mont.X86.Context
public import VerifiedGarbage.Proof.Mont.X86.Ops
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Workspace bounds for runtime modular arithmetic -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86

theorem slot_le {n i j : Nat} (h : i < j) : slot n i + stride n ≤ slot n j := by
  have := Nat.mul_le_mul_right (stride n) h
  simp only [slot, Nat.succ_mul] at *
  omega

theorem slot_bound {n i : Nat} (h : i < 9) : slot n i + stride n ≤ contextBytes n := slot_le h

theorem slot_sep {n i j : Nat} (h : i ≠ j) :
    slot n i + stride n ≤ slot n j ∨ slot n j + stride n ≤ slot n i := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact .inl (slot_le h)
  · exact .inr (slot_le h)

theorem slot_header (n i : Nat) : 64 ≤ slot n i := by unfold slot; omega

theorem context_accLen (n : Nat) : accLen (contextMod n) = 16 * n + 4 := by
  simp only [accLen, words, contextMod]
  omega

theorem context_opLay {n size o a b : Nat} (hs : contextBytes n ≤ size)
    (ho : o < 9) (ha : a < 9) (hb : b < 9) (ho2 : o ≠ 2) (ha2 : a ≠ 2) (hb2 : b ≠ 2)
    (ho1 : o ≠ 1) :
    OpLay (contextMod n) size (slot n 2) (slot n o) (slot n a) (slot n b) := by
  have b2 := slot_bound (n := n) (i := 2) (by decide)
  have bo := slot_bound (n := n) ho
  have ba := slot_bound (n := n) ha
  have bb := slot_bound (n := n) hb
  have so := slot_sep (n := n) ho2
  have sa := slot_sep (n := n) ha2
  have sb := slot_sep (n := n) hb2
  have sm := slot_sep (n := n) (i := 2) (j := 0) (by decide)
  have st := slot_sep (n := n) (i := 2) (j := 1) (by decide)
  have ot := slot_sep (n := n) ho1
  simp only [stride] at *
  constructor <;> simp only [accLen, words, contextMod] <;> omega

end VG.Proof.Mont.X86.Dynamic
