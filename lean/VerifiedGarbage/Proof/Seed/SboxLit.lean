import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Spec.Seed

/-! # SEED's S-boxes as a packed table

As RC2's PITABLE (`Proof/Rc2/PiLit.lean`): the kernel looks up
`Spec.Seed.s0` and `s1` slowly, flattening their rows again at every
lookup. `sNat` reads their entries from one number instead
(`materialize_table`, `Proof/Framework/Lit.lean`), checked once here against
the rows (`sTable_getD`).
-/

namespace VG.Proof.Seed

/-- The rows that `Spec.Seed.s0` and `s1` flatten (the values of their
`let`s), found by unification, with the proofs that they flatten them. -/
def s0RowsEq : { r : Vector (Vector Byte 16) 16 // Spec.Seed.s0 = r.flatten } := ⟨_, rfl⟩
def s1RowsEq : { r : Vector (Vector Byte 16) 16 // Spec.Seed.s1 = r.flatten } := ⟨_, rfl⟩

/-- SEED's S-box `S0` (`odd = false`) or `S1` (`odd = true`). -/
def sTable (odd : Bool) : Vector Byte 256 := if odd then Spec.Seed.s1 else Spec.Seed.s0

def sRows (odd : Bool) : Vector (Vector Byte 16) 16 := if odd then s1RowsEq.1 else s0RowsEq.1

theorem sTable_eq (odd : Bool) : sTable odd = (sRows odd).flatten := by
  cases odd
  · exact s0RowsEq.2
  · exact s1RowsEq.2

/-- Entry `j` of row `k % 16` of `S0` (`k < 16`) or `S1` (`k ≥ 16`), as a number. -/
def sRowNat (k j : Nat) : Nat :=
  (((sRows (16 ≤ k)).toArray.getD (k % 16) default).toArray.getD j 0).toNat

materialize_table sRowNat 32 16

/-- Entry `c` of the S-box, as a number. -/
def sNat (odd : Bool) (c : Nat) : Nat :=
  if c < 256 then sRowNat (16 * odd.toNat + c / 16) (c % 16) else 0

theorem sTable_getD (odd : Bool) (c : Nat) : (sTable odd).getD c 0 = BitVec.ofNat 8 (sNat odd c) := by
  rw [sNat]
  split
  · rename_i hc
    have hm : (16 * odd.toNat + c / 16) % 16 = c / 16 := by cases odd <;> simp <;> omega
    have hodd : decide (16 ≤ 16 * odd.toNat + c / 16) = odd := by
      cases odd <;> simp <;> omega
    rw [sRowNat, hodd, hm, Vector.getD, sTable_eq, Array.getD, dite_eq_left (by simpa using hc)]
    have h1 : c / 16 < (sRows odd).toArray.size := by simp only [Vector.size_toArray]; omega
    have e1 : (sRows odd).toArray.getD (c / 16) default = (sRows odd)[c / 16]'(by omega) := by
      unfold Array.getD; rw [dite_eq_left h1]; rfl
    have h2 : c % 16 < ((sRows odd)[c / 16]'(by omega)).toArray.size := by
      simp only [Vector.size_toArray]; omega
    have e2 : ((sRows odd)[c / 16]'(by omega)).toArray.getD (c % 16) 0 =
        ((sRows odd)[c / 16]'(by omega))[c % 16]'(by omega) := by
      unfold Array.getD; rw [dite_eq_left h2]; rfl
    rw [e1, e2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact Vector.getElem_flatten (xss := sRows odd) (by omega)
  · rename_i hc
    rw [Vector.getD, Array.getD, dite_eq_right (by simpa using hc)]
    rfl

end VG.Proof.Seed
