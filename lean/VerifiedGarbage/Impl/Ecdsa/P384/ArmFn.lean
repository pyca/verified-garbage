module

public import VerifiedGarbage.Impl.Ecdsa.P384.ArmComb
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.Impl.Residue.Arm
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.Arm
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Spec.Ecdsa.Verify.P384

/-!
# ECDSA over P-384 on 32-bit ARM, as emitted

`vg_ecdsa_p384_verify` and `vg_ecdsa_p384_sign`, with their `_umaal`
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

/-- `vg_ecdsa_p384_verify`. -/
def verifyP384 : Prog isa :=
  scrubF 32 96
    (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P384.inst.curve.len false Impl.Ecdsa.Arm.verifyP384Comb)

/-- `vg_ecdsa_p384_verify_umaal`. -/
def verifyP384U : Prog isa :=
  scrubF 32 96
    (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P384.inst.curve.len false Impl.Ecdsa.Arm.verifyP384CombU)

/-- The configuration of signing's code: the HMAC functions `f` of its table,
and its core with `umaal` if `u`. -/
def signCfgP384 (f : Impl.Ecdsa.Rfc6979.Arm.Fns) (u : Bool) : Impl.Ecdsa.Rfc6979.Arm.Cfg where
  f := f
  w := 2 * Impl.Ecdsa.Arm.p384.n - (if Impl.Ecdsa.Arm.p384.C.len = 28 then 1 else 0)
  len := Impl.Ecdsa.Arm.p384.C.len
  big := false
  sh := 0
  n := Impl.Ecdsa.Arm.p384.C.n
  tries := Spec.Ecdsa.Rfc6979.Curves.p384.tries
  coreN := bif u then "vg_ecdsa_p384_sign_k" ++ "_umaal" else "vg_ecdsa_p384_sign_k"
  coreC := bif u then Impl.Ecdsa.Arm.signP384CombU else Impl.Ecdsa.Arm.signP384Comb

/-- `vg_ecdsa_p384_sign`, calling the HMAC functions `f` through its table. -/
def signP384 (f : Impl.Ecdsa.Rfc6979.Arm.Fns) : Prog isa := scrubF 32 536 (signCfgP384 f false).sign

/-- `vg_ecdsa_p384_sign_umaal`, calling the HMAC functions `f` through its table. -/
def signP384U (f : Impl.Ecdsa.Rfc6979.Arm.Fns) : Prog isa := scrubF 32 536 (signCfgP384 f true).sign

end VG.Impl.Ecdsa.Arm.Fn
