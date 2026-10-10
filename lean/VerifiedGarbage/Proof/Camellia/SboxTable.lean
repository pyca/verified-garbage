import VerifiedGarbage.Spec.Camellia
import VerifiedGarbage.Proof.Framework.Bitslice.Table
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# `SBOX1` on all 256 inputs at once

The truth tables of the specification's `SBOX1` (bit `j` of the output on
each of the 256 inputs) and of the inputs (bit `k`), which each target's
proof of its S-box circuit compares the circuit's evaluation with.
-/

namespace VG.Proof.Camellia

open VG.Bitslice

/-- The truth table of bit `k` of the input. -/
def inT (k : Nat) : Nat := tableOf (fun c => c.testBit k) 256

/-- The table whose row `c` is `bs[c]` (`false` beyond them). -/
def tableOfList : List Bool → Nat
  | [] => 0
  | b :: bs => 2 * tableOfList bs + b.toNat

theorem testBit_tableOfList (bs : List Bool) (c : Nat) :
    (tableOfList bs).testBit c = bs.getD c false := by
  induction bs generalizing c with
  | nil => simp [tableOfList]
  | cons b bs ih =>
    cases c with
    | zero => cases b <;> simp [tableOfList]
    | succ c =>
      rw [tableOfList, Nat.testBit_succ, List.getD_cons_succ, ← ih]
      congr 1
      cases b <;> simp [Bool.toNat] <;> omega

/-- The truth table of bit `j` of `SBOX1`, read from the specification's
table in one pass: the kernel evaluates it in a fraction of a second, where
looking up `SBOX1` of each input (`Vector.getD`, which walks the table)
takes seconds per bit. -/
def sbox1T (j : Nat) : Nat := tableOfList (Spec.Camellia.sbox1Table.toList.map (·.getLsbD j))

theorem testBit_sbox1T {j c : Nat} (hc : c < 256) :
    (sbox1T j).testBit c = (Spec.Camellia.sbox1 (BitVec.ofNat 8 c)).getLsbD j := by
  have hl : Spec.Camellia.sbox1Table.toList.length = 256 := Vector.length_toList
  rw [sbox1T, testBit_tableOfList, Spec.Camellia.sbox1, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_eq_getElem (by omega), Option.map_some, Option.getD_some,
    Vector.getD, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c < 2 ^ 8), Array.getD,
    dite_eq_left_of_eq_true (eq_true (by simpa using hc))]
  rfl

end VG.Proof.Camellia

namespace VG

-- The tables, once, which both targets' checks read (`lit_decide`).
materialize_table Proof.Camellia.inT 8
materialize_table Proof.Camellia.sbox1T 8

end VG
