module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Hash
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.CT
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-!
# Deterministic ECDSA on 32-bit ARM: `Verified`

For any hash function `P`: `sign_ok` gives the contract's postcondition and
keeps the callee-saved registers and the stack pointer (`abiPreserved`), and
`sign_ct` constant time up to the number of candidates. Each instance's file
shows that its contract implies `rfcArm` (`sign_verified`'s `himp`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm

variable (P : RfcHash)

theorem sign_arm (s : State) (h : (rfcArm P.I (240 + 4 * P.e) P.R.coreConsts).pre s) :
    ∃ t s', Exec isa (cfgOf P).sign s t s' ∧ abiPreserved s s' ∧ (rfcArm P.I (240 + 4 * P.e) P.R.coreConsts).post s s' :=
  sign_ok (P := P) h

theorem sign_verified (himp : (rfcArm P.I (240 + 4 * P.e) P.R.coreConsts).Implies (P.I.signContract (Arm.abi.withConsts P.R.coreConsts) (240 + 4 * P.e))) :
    Verified Arm.target (cfgOf P).sign (P.I.signContract (Arm.abi.withConsts P.R.coreConsts) (240 + 4 * P.e)) :=
  Verified.of_correct (sign_arm P) sign_ct himp

end VG.Proof.Ecdsa.Rfc6979.Arm
