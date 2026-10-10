import VerifiedGarbage.Spec.Sm4
import VerifiedGarbage.Proof.Framework.Bitslice.Table

/-!
# The SM4 S-box on all 256 inputs at once

The truth tables of the specification's S-box (bit `j` of the output on each
of the 256 inputs) and of the inputs (bit `k`), which each target's proof of
its S-box circuit compares the circuit's evaluation with.
-/

namespace VG.Proof.Sm4

open VG.Bitslice

/-- The S-box on a byte. -/
def sboxB (x : Byte) : Byte := Spec.Sm4.sbox.getD x.toNat 0

/-- The truth table of bit `k` of the input. -/
def inT (k : Nat) : Nat := tableOf (fun c => c.testBit k) 256

/-- The truth table of bit `j` of the S-box. -/
def sboxT (j : Nat) : Nat := tableOf (fun c => (sboxB (BitVec.ofNat 8 c)).getLsbD j) 256

end VG.Proof.Sm4
