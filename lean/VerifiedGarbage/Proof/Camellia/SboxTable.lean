import VerifiedGarbage.Spec.Camellia
import VerifiedGarbage.Proof.Framework.Bitslice.Table

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

/-- The truth table of bit `j` of `SBOX1`. -/
def sbox1T (j : Nat) : Nat := tableOf (fun c => (Spec.Camellia.sbox1 (BitVec.ofNat 8 c)).getLsbD j) 256

end VG.Proof.Camellia
