module

public import VerifiedGarbage.Impl.Ecdsa.P521.ArmComb
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.Impl.Scrub.Arm
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.Arm
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Spec.Ecdsa.Verify.P521

/-!
# ECDSA over P-521 on 32-bit ARM, as emitted

`vg_ecdsa_p521_verify` and `vg_ecdsa_p521_sign`, with their `_umaal`
variants: each one's code, then the instructions that zero the stack its
contract reserves (96 bytes for verification, whose frame keeps the hash's
working values; 536 for signing, whose frames keep the nonce's HMAC states,
and those of the HMAC functions it calls through its table) and set the
registers a callee may change, but the result, and the flags to constants
(`Impl.Scrub.Arm.scrubAll`). Signing takes the HMAC functions of its table
(`f`), as its registration gives them.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- `vg_ecdsa_p521_verify`. -/
def verifyP521 : Prog isa :=
  scrubAll 32 96
    (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P521.inst.curve.len true Impl.Ecdsa.Arm.verifyP521Comb)

/-- `vg_ecdsa_p521_verify_umaal`. -/
def verifyP521U : Prog isa :=
  scrubAll 32 96
    (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P521.inst.curve.len true Impl.Ecdsa.Arm.verifyP521CombU)

/-- The configuration of signing's code: the HMAC functions `f` of its table,
and its core with `umaal` if `u`. -/
def signCfgP521 (f : Impl.Ecdsa.Rfc6979.Arm.Fns) (u : Bool) : Impl.Ecdsa.Rfc6979.Arm.Cfg where
  f := f
  w := 2 * Impl.Ecdsa.Arm.p521.n - (if Impl.Ecdsa.Arm.p521.C.len = 28 then 1 else 0)
  len := Impl.Ecdsa.Arm.p521.C.len
  big := true
  sh := 7
  n := Impl.Ecdsa.Arm.p521.C.n
  tries := Spec.Ecdsa.Rfc6979.Curves.p521.tries
  coreN := bif u then "vg_ecdsa_p521_sign_k" ++ "_umaal" else "vg_ecdsa_p521_sign_k"
  coreC := bif u then Impl.Ecdsa.Arm.signP521CombU else Impl.Ecdsa.Arm.signP521Comb

/-- `vg_ecdsa_p521_sign`, calling the HMAC functions `f` through its table. -/
def signP521 (f : Impl.Ecdsa.Rfc6979.Arm.Fns) : Prog isa := scrubAll 32 536 (signCfgP521 f false).sign

/-- `vg_ecdsa_p521_sign_umaal`, calling the HMAC functions `f` through its table. -/
def signP521U (f : Impl.Ecdsa.Rfc6979.Arm.Fns) : Prog isa := scrubAll 32 536 (signCfgP521 f true).sign

end VG.Impl.Ecdsa.Arm.Fn
