module
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The bytewise zero predicate agrees with DSA's integer decoder -/

@[expose] public section

namespace VG.Proof.Dsa
open VG

theorem decodeBE_eq_zero (bytes : List Byte) :
    Spec.Dsa.decodeBE bytes = 0 ↔ ∀ b ∈ bytes, b = 0 := by
  induction bytes with
  | nil => simp [Spec.Dsa.decodeBE]
  | cons b bs ih =>
    rw [decodeBE_os2ip, VG.Proof.RsaPss.os2ip_cons', ← decodeBE_os2ip]
    have hp : 0 < 256 ^ bs.length := Nat.pow_pos (by decide)
    have hb : b.toNat = 0 ↔ b = 0 :=
      ⟨fun h => BitVec.eq_of_toNat_eq h, fun h => congrArg BitVec.toNat h⟩
    rw [Nat.add_eq_zero_iff, Nat.mul_eq_zero, or_iff_left (Nat.ne_of_gt hp), hb, ih]
    simp only [List.mem_cons, forall_eq_or_imp]

end VG.Proof.Dsa
