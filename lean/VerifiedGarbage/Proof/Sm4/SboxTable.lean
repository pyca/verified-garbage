module

public import VerifiedGarbage.Spec.Sm4
meta import VerifiedGarbage.Spec.Sm4
public import VerifiedGarbage.Proof.Framework.Bitslice.Table
meta import VerifiedGarbage.Proof.Framework.Bitslice.Table
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The SM4 S-box on all 256 inputs at once

The truth tables of the specification's S-box (bit `j` of the output on each
of the 256 inputs) and of the inputs (bit `k`), which each target's proof of
its S-box circuit compares the circuit's evaluation with. The kernel
evaluates them once, here (`materialize_table`), rather than evaluate the
specification's S-box on every input again for every target.
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG.Bitslice

/-- The S-box on a byte. -/
def sboxB (x : Byte) : Byte := Spec.Sm4.sbox.getD x.toNat 0

/-- The truth table of bit `k` of the input. -/
def inT (k : Nat) : Nat := tableOf (fun c => c.testBit k) 256

/-- The S-box's rows, as the specification writes them: `sbox` is their
`flatten`, an array built by 256 `push`es, each of which the kernel
evaluates by rebuilding the list of what was pushed before it. -/
def sboxRows : { r : Vector (Vector Byte 16) 16 // Spec.Sm4.sbox = r.flatten } :=
  ⟨_, Spec.Sm4.sbox.eq_1⟩

/-- The specification's S-box as a list (`sboxL_eq`), from its rows by
operations on lists, which the kernel evaluates in one pass (and once:
`materialize_value` below). -/
def sboxL : List Byte := (sboxRows.1.toList.map Vector.toList).flatten

/-- The list of a vector of rows, by operations on lists. -/
theorem toList_flatten_rows {α : Type} {n m : Nat} (r : Vector (Vector α n) m) :
    r.flatten.toList = (r.toList.map Vector.toList).flatten := by
  simp only [Vector.flatten, Vector.toList, Array.toList_flatten, Array.toList_map, List.map_map,
    Function.comp_def]
  rfl

theorem sboxL_eq : sboxL = Spec.Sm4.sbox.toList :=
  (toList_flatten_rows sboxRows.1).symm.trans (congrArg Vector.toList sboxRows.2).symm

/-- Bytes packed in one number, the first lowest. -/
def packL : List Byte → Nat
  | [] => 0
  | b :: l => b.toNat + 256 * packL l

/-- Byte `c` of the packed bytes, read by a shift (zero beyond them, as `getD`). -/
theorem packL_shift (l : List Byte) (c : Nat) : packL l >>> (8 * c) % 256 = (l.getD c 0).toNat := by
  induction l generalizing c with
  | nil => simp [packL]
  | cons b l ih =>
    have hb := b.isLt
    cases c with
    | zero => simp only [packL, Nat.mul_zero, Nat.shiftRight_zero, List.getD_cons_zero]; omega_using [hb]
    | succ c =>
      rw [List.getD_cons_succ, ← ih, packL, Nat.mul_add, Nat.mul_one, Nat.add_comm (8 * c) 8,
        Nat.shiftRight_add]
      congr 2
      rw [Nat.shiftRight_eq_div_pow]
      omega_using [hb]

/-- The S-box packed in one number (`materialize_value` below), in which the
kernel reads an entry by a shift rather than by walking the list to it. -/
def sboxP : Nat := packL sboxL

/-- The S-box on input `c`, as a number. -/
def sboxN (c : Nat) : Nat := sboxP >>> (8 * c) % 256

/-- A vector's entries are its list's, for any vector: stated for `Spec.Sm4.sbox`
directly, the kernel's check of the `simp` proof took seconds. -/
theorem toList_getD_toNat (v : Vector Byte 256) (c : Nat) :
    (v.toList.getD c 0).toNat = (v.getD c 0).toNat := by
  simp [Vector.getD, Array.getD_eq_getD_getElem?]

/-- `sboxN` is the specification's S-box, at every index. -/
theorem sboxN_getD (c : Nat) : sboxN c = (Spec.Sm4.sbox.getD c 0).toNat := by
  rw [sboxN, sboxP, packL_shift, sboxL_eq]
  exact toList_getD_toNat _ _

theorem sboxN_eq {c : Nat} (hc : c < 256) : sboxN c = (sboxB (BitVec.ofNat 8 c)).toNat := by
  rw [sboxN_getD, sboxB, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hc])]

/-- The truth table of bit `j` of the S-box. -/
def sboxT (j : Nat) : Nat := tableOf (fun c => (sboxN c).testBit j) 256

end VG.Proof.Sm4

namespace VG

materialize_value Proof.Sm4.sboxL
materialize_value Proof.Sm4.sboxP
materialize_table Proof.Sm4.sboxN 256
materialize_table Proof.Sm4.inT 8
materialize_table Proof.Sm4.sboxT 8

end VG
