module
import VerifiedGarbage.Proof.Mont.X86.Words
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeLayout
public import VerifiedGarbage.Proof.Mont.Words

/-! # Values written into the primality header, including q160's witness cursor -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem readW_writeW_aligned32 (mem : Mem) (base : Addr) (read write : Nat) (value : BitVec 32)
    (ra : read % 4 = 0) (wa : write % 4 = 0)
    (rb : read + 4 ≤ 2 ^ 64) (wb : write + 4 ≤ 2 ^ 64) :
    (mem.writeW (off base write) value).readW (off base read) 32 =
      if read = write then value else mem.readW (off base read) 32 := by
  by_cases same : read = write
  · subst read; rw [Mem.readW_writeW_self32, ite_eq_left rfl]
  · rw [Mem.readW_writeW_sep (Offset.sep base (by omega) rb wb) (by decide), ite_eq_right same]

theorem primeTapeValues {s t : Mem} {base : Addr} {words : Nat → BitVec 32}
    (mem : t = (((s.writeW (off base primeTape) (words 13)).writeW
      (off base primeTapeLen) (words 15)).writeW (off base primeUsed) (words 16)).writeW
        (off base primeWitness) (words 5 + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.witness)) :
    t.readW (off base primeTape) 32 = words 13 ∧
      t.readW (off base primeTapeLen) 32 = words 15 ∧
      t.readW (off base primeUsed) 32 = words 16 ∧
      t.readW (off base primeWitness) 32 = words 5 + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.witness := by
  rw [mem]
  constructor
  · rw [readW_writeW_aligned32 _ _ primeTape primeWitness _ (by decide) (by decide) (by decide) (by decide),
      ite_eq_right (by decide), readW_writeW_aligned32 _ _ primeTape primeUsed _ (by decide) (by decide) (by decide) (by decide),
      ite_eq_right (by decide), readW_writeW_aligned32 _ _ primeTape primeTapeLen _ (by decide) (by decide) (by decide) (by decide),
      ite_eq_right (by decide), Mem.readW_writeW_self32]
  constructor
  · rw [readW_writeW_aligned32 _ _ primeTapeLen primeWitness _ (by decide) (by decide) (by decide) (by decide),
      ite_eq_right (by decide), readW_writeW_aligned32 _ _ primeTapeLen primeUsed _ (by decide) (by decide) (by decide) (by decide),
      ite_eq_right (by decide), Mem.readW_writeW_self32]
  constructor
  · rw [readW_writeW_aligned32 _ _ primeUsed primeWitness _ (by decide) (by decide) (by decide) (by decide),
      ite_eq_right (by decide), Mem.readW_writeW_self32]
  · exact Mem.readW_writeW_self32 _ _ _
end VG.Proof.Dsa.X86.Generation
