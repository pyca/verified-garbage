module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtValidateStage
public import VerifiedGarbage.Proof.Bignum.CrtResult
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Accepted factors are safe odd moduli for both private powers -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont

theorem CrtShared.accepted_factors {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (accepted : crtAccepted bs) :
    (1 < Spec.Rsa.os2ip (bs 2) ∧ Spec.Rsa.os2ip (bs 2) % 2 = 1) ∧
    (1 < Spec.Rsa.os2ip (bs 3) ∧ Spec.Rsa.os2ip (bs 3) % 2 = 1) := by
  have plen := (h.buffers.source 2).length
  have qlen := (h.buffers.source 3).length
  obtain ⟨odd, _, pSmall, qSmall⟩ := crt_bounds_of h.valid h.buffers.lengthValid.1
    plen h.buffers.pShort qlen h.buffers.qShort
  exact ⟨factor_facts (by rw [Nat.mul_comm]; exact accepted.2.2) qSmall odd,
    factor_facts accepted.2.2 pSmall odd⟩

end VG.Proof.Bignum.Arm
