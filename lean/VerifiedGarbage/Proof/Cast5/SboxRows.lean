module

public import VerifiedGarbage.Spec.Cast5
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Spec.Cast5
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# CAST5's S-boxes as lists

The specification's S-boxes are vectors flattened from their printed rows
(`Vector.flatten`, which appends arrays one element at a time: the kernel,
reading the list of such an array, takes a step for every element before
each one it reads, 32,000 for an S-box). `sboxRows` is their lists, read
from the rows instead (`List.flatten`), and has a literal.
-/

@[expose] public section

namespace VG.Proof.Cast5

open Spec.Cast5 (Word)

/-- The list of a flattened vector, from its rows' lists. -/
theorem toList_flatten {α : Type} {n m : Nat} (rows : Vector (Vector α m) n) :
    rows.flatten.toList = (rows.toList.map Vector.toList).flatten := by
  rcases rows with ⟨rows, rfl⟩
  simp only [Vector.flatten, Vector.toList, Array.toList_flatten, Array.toList_map, List.map_map]
  rfl

/-! Each S-box's list, from its rows (found by unfolding the S-box). -/

def s1L : { l : List Word // Spec.Cast5.s1.toList = l } := ⟨_, toList_flatten _⟩
def s2L : { l : List Word // Spec.Cast5.s2.toList = l } := ⟨_, toList_flatten _⟩
def s3L : { l : List Word // Spec.Cast5.s3.toList = l } := ⟨_, toList_flatten _⟩
def s4L : { l : List Word // Spec.Cast5.s4.toList = l } := ⟨_, toList_flatten _⟩
def s5L : { l : List Word // Spec.Cast5.s5.toList = l } := ⟨_, toList_flatten _⟩
def s6L : { l : List Word // Spec.Cast5.s6.toList = l } := ⟨_, toList_flatten _⟩
def s7L : { l : List Word // Spec.Cast5.s7.toList = l } := ⟨_, toList_flatten _⟩
def s8L : { l : List Word // Spec.Cast5.s8.toList = l } := ⟨_, toList_flatten _⟩

/-- The S-boxes' lists, read from the rows. (A constant: a literal stated
for a list, `materialize_value N := [a, …]`, would make every definition
that builds a list lead to it.) -/
def sboxRows : List (List Word) := [s1L.1, s2L.1, s3L.1, s4L.1, s5L.1, s6L.1, s7L.1, s8L.1]

materialize_value sboxRows

end VG.Proof.Cast5
