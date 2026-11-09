module

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Rows
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
public import VerifiedGarbage.Proof.MlKem.NttLayer
import VerifiedGarbage.Proof.MlKem.AArch64.Barrett
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# ML-KEM's 16-bit NTT on AArch64: lanes reduced to `[0, q)`

A lane less than `q` in absolute value made nonnegative (`nonneg_lane`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open Impl.MlKem.AArch64.Ntt16

/-! ## Reduction to `[0, q)` -/

/-- A lane less than `q` in absolute value made nonnegative: `r + (r >> 15 & q)`. -/
theorem nonneg_lane {r : BitVec 16} (h1 : -3329 < r.toInt) (h2 : r.toInt < 3329) :
    (r + (r.sshiftRight 15 &&& BitVec.ofNat 16 3329)).toInt =
      if r.toInt < 0 then r.toInt + 3329 else r.toInt := by
  rw [BitVec.sshiftRight_eq, Int.shiftRight_eq_div_pow]
  by_cases h : r.toInt < 0
  · rw [show r.toInt / ((2 ^ 15 : Nat) : Int) = -1 by omega_arith, ite_eq_left h,
      show BitVec.ofInt 16 (-1) &&& BitVec.ofNat 16 3329 = BitVec.ofNat 16 3329 by decide,
      BitVec.toInt_add]
    simp only [Int.bmod_def, show (BitVec.ofNat 16 3329).toInt = 3329 by decide]
    split <;> omega_arith
  · rw [show r.toInt / ((2 ^ 15 : Nat) : Int) = 0 by omega_arith, ite_eq_right h,
      show BitVec.ofInt 16 0 &&& BitVec.ofNat 16 3329 = 0#16 by decide, BitVec.add_zero]

end VG.Proof.MlKem.AArch64.Ntt16
