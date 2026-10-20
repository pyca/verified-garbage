module

public import VerifiedGarbage.Proof.MillerRabin.X86.TableMath

/-! # The exponent loop retains the table and constants while the witness is selected anew -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Impl.MillerRabin.X86

def runArrays : List Nat := [aY, aOne, aMinusOne, aExponent, 0] ++ (List.range 16).map (aTable + ·)

def runValues (A : Nat → Nat) (c w : Nat) : Nat → Nat := setAt (tableValues A c w 14) aY (A aOne)

theorem runArrays_y : aY ∈ runArrays := by simp [runArrays]
theorem runArrays_one : aOne ∈ runArrays := by simp [runArrays]
theorem runArrays_minus : aMinusOne ∈ runArrays := by simp [runArrays]
theorem runArrays_exp : aExponent ∈ runArrays := by simp [runArrays]

theorem runArrays_power {j : Nat} (digit : j < 16) : aTable + j ∈ runArrays := by
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr digit, rfl⟩

theorem runArrays_notX : aX ∉ runArrays := by
  intro mem
  rcases List.mem_append.mp mem with mem | mem
  · change 5 ∈ [6, 9, 10, 27, 0] at mem
    contradiction
  · obtain ⟨j, _, eq⟩ := List.mem_map.mp mem
    unfold aTable aX at eq
    omega

theorem runValues_y (A : Nat → Nat) (c w : Nat) : runValues A c w aY = A aOne := setAt_self _ _ _
theorem runValues_one (A : Nat → Nat) (c w : Nat) : runValues A c w aOne = A aOne := rfl
theorem runValues_minus (A : Nat → Nat) (c w : Nat) : runValues A c w aMinusOne = A aMinusOne := rfl
theorem runValues_exp (A : Nat → Nat) (c w : Nat) : runValues A c w aExponent = A aExponent := rfl

theorem runValues_power (A : Nat → Nat) (c w : Nat) {j : Nat} (digit : j < 16) :
    runValues A c w (aTable + j) = Word32.tp c w (A aX) (A aOne) j := by
  rw [runValues, setAt_other _ _ (by unfold aTable aY; omega), tableValues_power A c w digit]

theorem runValues_identity (A : Nat → Nat) (c w : Nat) : runValues A c w aY = runValues A c w aTable := by
  rw [runValues_y, show aTable = aTable + 0 by omega, runValues_power A c w (by decide : 0 < 16)]
  rfl

end VG.Proof.MillerRabin.X86
