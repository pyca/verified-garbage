module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.ArmComb
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.Impl.Residue.Arm
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.Arm
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP320r1

/-!
# ECDSA over brainpoolP320r1 on 32-bit ARM, as emitted

`vg_ecdsa_brainpoolp320r1_verify` and `vg_ecdsa_brainpoolp320r1_sign`, with their `_umaal`
variants: each one's code, then the instructions that zero the stack its
contract reserves (96 bytes for verification, whose frame keeps the hash's
working values; 536 for signing, whose frames keep the nonce's HMAC states,
and those of the HMAC functions it calls through its table) and set the
registers a callee may change, but the result, and the flags to constants
(`Impl.Residue.Arm.scrubF`). Signing takes the HMAC functions of its table
(`f`), as its registration gives them.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm

/-- `vg_ecdsa_brainpoolp320r1_verify`. -/
def verifyBrainpoolP320r1 : Prog isa :=
  scrubF 32 96
    (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP320r1.inst.curve.len false Impl.Ecdsa.Arm.verifyBrainpoolP320r1Comb)

/-- `vg_ecdsa_brainpoolp320r1_verify_umaal`. -/
def verifyBrainpoolP320r1U : Prog isa :=
  scrubF 32 96
    (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP320r1.inst.curve.len false Impl.Ecdsa.Arm.verifyBrainpoolP320r1CombU)

/-- The configuration of signing's code: the HMAC functions `f` of its table,
and its core with `umaal` if `u`. -/
def signCfgBrainpoolP320r1 (f : Impl.Ecdsa.Rfc6979.Arm.Fns) (u : Bool) : Impl.Ecdsa.Rfc6979.Arm.Cfg where
  f := f
  w := 2 * Impl.Ecdsa.Arm.brainpoolp320r1.n - (if Impl.Ecdsa.Arm.brainpoolp320r1.C.len = 28 then 1 else 0)
  len := Impl.Ecdsa.Arm.brainpoolp320r1.C.len
  big := false
  sh := 0
  n := Impl.Ecdsa.Arm.brainpoolp320r1.C.n
  tries := Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1.tries
  coreN := bif u then "vg_ecdsa_brainpoolp320r1_sign_k" ++ "_umaal" else "vg_ecdsa_brainpoolp320r1_sign_k"
  coreC := bif u then Impl.Ecdsa.Arm.signBrainpoolP320r1CombU else Impl.Ecdsa.Arm.signBrainpoolP320r1Comb

/-- `vg_ecdsa_brainpoolp320r1_sign`, calling the HMAC functions `f` through its table. -/
def signBrainpoolP320r1 (f : Impl.Ecdsa.Rfc6979.Arm.Fns) : Prog isa := scrubF 32 536 (signCfgBrainpoolP320r1 f false).sign

/-- `vg_ecdsa_brainpoolp320r1_sign_umaal`, calling the HMAC functions `f` through its table. -/
def signBrainpoolP320r1U (f : Impl.Ecdsa.Rfc6979.Arm.Fns) : Prog isa := scrubF 32 536 (signCfgBrainpoolP320r1 f true).sign

end VG.Impl.Ecdsa.Arm.Fn
