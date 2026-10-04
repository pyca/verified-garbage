import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Spec.Rc2

/-! # RC2's PITABLE as a packed table

The kernel looks up `Spec.Rc2.piTable` slowly: at every lookup it flattens
its rows again (quadratically, as `Array.push` on a literal array copies it)
and walks the list to the entry, seconds for the 256 lookups of the code of
each target. `piNat` reads the entries from one number instead
(`materialize_table`, `Proof/Framework/Lit.lean`), checked once here against
the rows, and each target's literals read the lookups through it
(`piTable_getD`).
-/

namespace VG.Rc2

/-- The rows that `Spec.Rc2.piTable` flattens (the value of its `let`), found
by unification, with the proof that it flattens them. -/
def piRowsEq : { r : Vector (Vector Byte 16) 16 // Spec.Rc2.piTable = r.flatten } := ⟨_, rfl⟩

/-- The rows of `Spec.Rc2.piTable`. -/
def piRows : Vector (Vector Byte 16) 16 := piRowsEq.1

theorem piTable_eq : Spec.Rc2.piTable = piRows.flatten := piRowsEq.2

/-- Entry `j` of row `i` of PITABLE, as a number. -/
def piRowNat (i j : Nat) : Nat := ((piRows.toArray.getD i default).toArray.getD j 0).toNat

materialize_table piRowNat 16 16

/-- PITABLE's entry `i`, as a number. -/
def piNat (i : Nat) : Nat := if i < 256 then piRowNat (i / 16) (i % 16) else 0

theorem piTable_getD (i : Nat) : Spec.Rc2.piTable.getD i 0 = BitVec.ofNat 8 (piNat i) := by
  rw [piNat]
  split
  · rename_i hi
    rw [piRowNat, Vector.getD, piTable_eq, Array.getD, dite_eq_left (by simpa using hi)]
    have h1 : i / 16 < piRows.toArray.size := by simp only [Vector.size_toArray]; omega
    have e1 : piRows.toArray.getD (i / 16) default = piRows[i / 16]'(by omega) := by
      unfold Array.getD; rw [dite_eq_left h1]; rfl
    have h2 : i % 16 < (piRows[i / 16]'(by omega)).toArray.size := by
      simp only [Vector.size_toArray]; omega
    have e2 : (piRows[i / 16]'(by omega)).toArray.getD (i % 16) 0 =
        (piRows[i / 16]'(by omega))[i % 16]'(by omega) := by
      unfold Array.getD; rw [dite_eq_left h2]; rfl
    rw [e1, e2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact Vector.getElem_flatten (xss := piRows) (by omega)
  · rename_i hi
    rw [Vector.getD, Array.getD, dite_eq_right (by simpa using hi)]
    rfl

end VG.Rc2
