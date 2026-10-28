module
public import VerifiedGarbage.Proof.Bignum.CrtResult
public import VerifiedGarbage.Proof.Bignum.Arm.CrtValidateStage

import VerifiedGarbage.Proof.Bignum.Arm.CrtCoefficientMath
import VerifiedGarbage.Proof.Bignum.Arm.CrtAcceptedFactors
import VerifiedGarbage.Proof.Bignum.Octets

/-! # Accepted CRT reconstruction fits the original RSA output width -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm

def crtPrivateValue (bs : Fin 7 → List Byte) : Nat :=
  crtResult (Spec.Rsa.os2ip (bs 2)) (Spec.Rsa.os2ip (bs 3)) (Spec.Rsa.os2ip (bs 4))
    (Spec.Rsa.os2ip (bs 5)) (Spec.Rsa.os2ip (bs 6)) (Spec.Rsa.os2ip (bs 1))

theorem crt_result_lt {P Q dp dq qi c : Nat} (p : 0 < P) (q : 0 < Q) :
    crtResult P Q dp dq qi c < P * Q := by
  let a := c ^ dp % P
  let b := c ^ dq % Q
  let h := ((((a : Int) - b) * qi) % (P : Int)).toNat
  have bh : b < Q := Nat.mod_lt _ q
  have hh : h < P := by
    rw [show h = ((a + P - b % P) % P * qi) % P from (crt_coefficient_value p).symm]
    exact Nat.mod_lt _ p
  have mul := Nat.mul_le_mul_left Q (by omega : h + 1 ≤ P)
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm Q P] at mul
  change b + Q * h < P * Q
  omega

theorem CrtShared.result_fits {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (accepted : crtAccepted bs) : crtPrivateValue bs < 2 ^ (8 * g.length) := by
  obtain ⟨p, q⟩ := h.accepted_factors accepted
  have result := crt_result_lt (dp := Spec.Rsa.os2ip (bs 4)) (dq := Spec.Rsa.os2ip (bs 5))
    (qi := Spec.Rsa.os2ip (bs 6)) (c := Spec.Rsa.os2ip (bs 1)) (by omega : 0 < Spec.Rsa.os2ip (bs 2))
    (by omega : 0 < Spec.Rsa.os2ip (bs 3))
  rw [accepted.2.2] at result
  have size := os2ip_lt (bs 0)
  rw [(h.buffers.source 0).length, pow256_eq] at size
  exact Nat.lt_trans result size

end VG.Proof.Bignum.Arm
