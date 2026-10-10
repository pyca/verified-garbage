import VerifiedGarbage.Spec.Sm4
import VerifiedGarbage.Proof.Framework.Bitslice.Table
import VerifiedGarbage.Proof.Framework.Lit

/-!
# The SM4 S-box on all 256 inputs at once

The truth tables of the specification's S-box (bit `j` of the output on each
of the 256 inputs) and of the inputs (bit `k`), which each target's proof of
its S-box circuit compares the circuit's evaluation with. The kernel
evaluates them once, here (`materialize_table`), rather than evaluate the
specification's S-box on every input again for every target.
-/

namespace VG.Proof.Sm4

open VG.Bitslice

/-- The S-box on a byte. -/
def sboxB (x : Byte) : Byte := Spec.Sm4.sbox.getD x.toNat 0

/-- The truth table of bit `k` of the input. -/
def inT (k : Nat) : Nat := tableOf (fun c => c.testBit k) 256

/-- The specification's S-box as a list, evaluated once (`materialize_value`
below): each lookup into `Spec.Sm4.sbox` would build its rows again. -/
def sboxL : List Byte := Spec.Sm4.sbox.toList

/-- The S-box on input `c`, as a number, from `sboxL`. -/
def sboxN (c : Nat) : Nat := (sboxL.getD c 0).toNat

theorem sboxN_eq {c : Nat} (hc : c < 256) : sboxN c = (sboxB (BitVec.ofNat 8 c)).toNat := by
  simp [sboxN, sboxL, sboxB, Nat.mod_eq_of_lt hc, Vector.getD, Array.getD_eq_getD_getElem?]

/-- The truth table of bit `j` of the S-box. -/
def sboxT (j : Nat) : Nat := tableOf (fun c => (sboxN c).testBit j) 256

end VG.Proof.Sm4

namespace VG

materialize_value Proof.Sm4.sboxL
materialize_table Proof.Sm4.sboxN 256
materialize_table Proof.Sm4.inT 8
materialize_table Proof.Sm4.sboxT 8

end VG
