module

public import VerifiedGarbage.Impl.Cast5.AArch64.Tbl
public import VerifiedGarbage.Impl.Cast5.AArch64.TblModes
public import VerifiedGarbage.Impl.Cast5.AArch64.TblKey
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Cast5.AArch64.Tbl
meta import VerifiedGarbage.Impl.Cast5.AArch64.TblModes
meta import VerifiedGarbage.Impl.Cast5.AArch64.TblKey
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! Literal code for the kernel-evaluated checks (constant time, `spSafe`, the ABI) of the code
that reads the S-boxes by `tbl`. -/

@[expose] public section

namespace VG

/-! The S-boxes' entries, as lists. The specification's S-boxes are vectors
flattened from their printed rows (`Vector.flatten`, which appends arrays one
element at a time: the kernel, reading the list of such an array, takes a step
for every element before each one it reads, 32,000 for an S-box). The lists
are read from the rows instead (`List.flatten`), and are the literal of
`sboxes`, which the table below and the code that carries it read. -/

namespace Proof.Cast5.AArch64.Tbl

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

/-- `Impl.Cast5.AArch64.Tbl.sboxes`, read from the rows. (A constant: a
literal stated for a list, `materialize_value N := [a, …]`, would make every
definition that builds a list lead to it.) -/
def sboxRows : List (List Word) := [s1L.1, s2L.1, s3L.1, s4L.1, s5L.1, s6L.1, s7L.1, s8L.1]

materialize_value sboxRows

end Proof.Cast5.AArch64.Tbl

noncomputable abbrev Impl.Cast5.AArch64.Tbl.sboxes.lit : List (List Spec.Cast5.Word) :=
  Proof.Cast5.AArch64.Tbl.sboxRows.lit

open Proof.Cast5.AArch64.Tbl in
theorem Impl.Cast5.AArch64.Tbl.sboxes.lit_eq :
    Impl.Cast5.AArch64.Tbl.sboxes = Impl.Cast5.AArch64.Tbl.sboxes.lit := by
  rw [Impl.Cast5.AArch64.Tbl.sboxes, s1L.2, s2L.2, s3L.2, s4L.2, s5L.2, s6L.2, s7L.2, s8L.2]
  exact sboxRows.lit_eq

/-! The table every load carries, evaluated once. -/

materialize_value Impl.Cast5.AArch64.Tbl.planeWords

/-! Quote table loads with the existing checked table literal. Reifying its
1,024 words separately at every load dominates quoting the round code. -/

open Lean in
@[instance_reducible] private meta def tblInstrToExpr : ToExpr AArch64.Instr :=
  let ordinary : ToExpr AArch64.Instr := inferInstance
  { ordinary with toExpr := fun i => match i with
    | .ldrqTbl t n off name words =>
      if name == Impl.Cast5.AArch64.Tbl.planesSym && words == Impl.Cast5.AArch64.Tbl.planeWords then
        mkApp5 (mkConst ``AArch64.Instr.ldrqTbl) (toExpr t) (toExpr n) (toExpr off) (toExpr name)
          (mkConst ``Impl.Cast5.AArch64.Tbl.planeWords.lit)
      else ordinary.toExpr i
    | _ => ordinary.toExpr i }

attribute [local instance] tblInstrToExpr

/-! The functions. -/

materialize_code Impl.Cast5.AArch64.Tbl.ecbEncrypt
materialize_code Impl.Cast5.AArch64.Tbl.ecbDecrypt

/-! The batches, whose registers `crypt`'s proof checks, and the modes over them. -/

materialize_code Impl.Cast5.AArch64.Tbl.batchEnc
materialize_code Impl.Cast5.AArch64.Tbl.batchDec
materialize_code Impl.Cast5.AArch64.Tbl.cbcDecryptChained
materialize_code Impl.Cast5.AArch64.Tbl.cfbDecrypt

/-! Key expansion, and the lookups it calls, evaluated once. -/

materialize_value Impl.Cast5.AArch64.Tbl.sboxes5678
materialize_code Impl.Cast5.AArch64.Tbl.expandKey

end VG
