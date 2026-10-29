module

public import VerifiedGarbage.Proof.MillerRabin.X86.Data
public import VerifiedGarbage.Proof.MillerRabin.Word32

/-! # The table's fourteen products extend one power at a time -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Impl.MillerRabin.X86

def tableValues (A : Nat → Nat) (c w k : Nat) (j : Nat) : Nat :=
  if j = aY then Word32.tp c w (A aX) (A aOne) (k + 1)
  else if aTable ≤ j ∧ j < aTable + k + 2 then Word32.tp c w (A aX) (A aOne) (j - aTable)
  else A j

def initialArrays : List Nat := [0, aX, aOne, aMinusOne, aExponent]

def tableArrays (k : Nat) : List Nat :=
  aY :: (List.range (k + 2)).map (aTable + ·) ++ initialArrays

theorem tableValues_y (A : Nat → Nat) (c w k : Nat) :
    tableValues A c w k aY = Word32.tp c w (A aX) (A aOne) (k + 1) := by
  simp only [tableValues, ↓reduceIte]

theorem tableValues_x (A : Nat → Nat) (c w k : Nat) : tableValues A c w k aX = A aX := by
  simp only [tableValues, aX, aY, aTable, show ¬ 5 = 6 by decide, show ¬ 11 ≤ 5 by decide,
    false_and, ↓reduceIte]

theorem tableValues_next (A : Nat → Nat) (c w k : Nat) :
    setAt (setAt (tableValues A c w k) aY
      (Word32.mm c w (tableValues A c w k aY) (tableValues A c w k aX)))
      (aTable + k + 2) (Word32.mm c w (tableValues A c w k aY) (tableValues A c w k aX)) =
    tableValues A c w (k + 1) := by
  rw [tableValues_y, tableValues_x]
  change setAt (setAt (tableValues A c w k) aY (Word32.tp c w (A aX) (A aOne) (k + 2)))
    (aTable + k + 2) (Word32.tp c w (A aX) (A aOne) (k + 2)) = _
  funext j
  unfold setAt tableValues
  by_cases output : j = aTable + k + 2
  · subst j
    simp only [show ¬ aTable + k + 2 = aY by unfold aTable aY; omega, ↓reduceIte]
    rw [ite_eq_left (by omega : aTable ≤ aTable + k + 2 ∧ aTable + k + 2 < aTable + (k + 1) + 2)]
    congr 1
    omega
  · rw [ite_eq_right output]
    by_cases y : j = aY
    · subst j
      simp only [↓reduceIte]
    · simp only [y, ↓reduceIte]
      have same : (aTable ≤ j ∧ j < aTable + k + 2) ↔ (aTable ≤ j ∧ j < aTable + (k + 1) + 2) := by omega
      simp only [same]

theorem tableArrays_next (k j : Nat) : j ∈ tableArrays (k + 1) ↔
    j = aTable + k + 2 ∨ j ∈ tableArrays k := by
  unfold tableArrays
  rw [show k + 1 + 2 = (k + 2) + 1 by omega, List.range_succ, List.map_append]
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
  rw [show aTable + (k + 2) = aTable + k + 2 by omega]
  simp only [or_left_comm, or_comm]

theorem tableValues_initial (A : Nat → Nat) (c w j : Nat) (known : j ∈ tableArrays 0) :
    setAt (setAt (setAt A aTable (A aOne)) (aTable + 1) (A aX)) aY (A aX) j =
      tableValues A c w 0 j := by
  change j ∈ [6, 11, 12, 0, 5, 9, 10, 27] at known
  simp only [List.mem_cons, List.not_mem_nil, or_false] at known
  rcases known with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem tableValues_power (A : Nat → Nat) (c w : Nat) {j : Nat} (digit : j < 16) :
    tableValues A c w 14 (aTable + j) = Word32.tp c w (A aX) (A aOne) j := by
  unfold tableValues
  rw [ite_eq_right (by unfold aTable aY; omega : aTable + j ≠ aY),
    ite_eq_left (by omega : aTable ≤ aTable + j ∧ aTable + j < aTable + 14 + 2)]
  congr 1
  omega

end VG.Proof.MillerRabin.X86
