module

public import VerifiedGarbage.Spec.Sm4
meta import VerifiedGarbage.Spec.Sm4
public import VerifiedGarbage.Proof.Framework.Bitslice.Table
meta import VerifiedGarbage.Proof.Framework.Bitslice.Table
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

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

/-- The specification's S-box as a list, evaluated once (`materialize_value`
below): each lookup into `Spec.Sm4.sbox` would build its rows again. -/
def sboxL : List Byte := Spec.Sm4.sbox.toList

/-- The S-box on input `c`, as a number, from `sboxL`. -/
def sboxN (c : Nat) : Nat := (sboxL.getD c 0).toNat

/-- A vector's entries are its list's, for any vector: stated for `Spec.Sm4.sbox`
directly, the kernel's check of the `simp` proof took seconds. -/
theorem toList_getD_toNat (v : Vector Byte 256) (c : Nat) :
    (v.toList.getD c 0).toNat = (v.getD c 0).toNat := by
  simp [Vector.getD, Array.getD_eq_getD_getElem?]

theorem sboxN_eq {c : Nat} (hc : c < 256) : sboxN c = (sboxB (BitVec.ofNat 8 c)).toNat := by
  unfold sboxN sboxB sboxL
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact toList_getD_toNat _ _

/-- The truth table of bit `j` of the S-box. -/
def sboxT (j : Nat) : Nat := tableOf (fun c => (sboxN c).testBit j) 256

end VG.Proof.Sm4

namespace VG

materialize_value Proof.Sm4.sboxL
materialize_table Proof.Sm4.sboxN 256
materialize_table Proof.Sm4.inT 8
materialize_table Proof.Sm4.sboxT 8

end VG
