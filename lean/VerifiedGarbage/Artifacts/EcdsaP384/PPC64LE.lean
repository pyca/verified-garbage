module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P384.PPC64LE
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.P384
public import VerifiedGarbage.Impl.Ecdsa.Verify.P384.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P384.Verified
public import VerifiedGarbage.Spec.Ecdsa.Verify.P384
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P384.Lit
public import VerifiedGarbage.Proof.P384.PPC64LE.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P384
public import VerifiedGarbage.Proof.HmacTable.PPC64LE.Vars
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384.CombLit

/-! # ECDSA over P-384 (FIPS 186-5) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcdsaP384.PPC64LE

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (signCodeT stackT OK p384R p384T_verified)
open VG.Proof.HmacTable.PPC64LE (vars tables names)

open VG.Proof.P384.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P384.verifyHashApi.artifact PPC64LE.target {
    code := Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.P384.inst.curve.len false
      Impl.Ecdsa.Verify.PPC64LE.verifyP384
    stack := 112
    verified := Proof.Ecdsa.Verify.PPC64LE.P384.verifyHash_verified hasLaw.law }] ++
  (if hv : OK vars ∧ "VG_P384_COMB" ∉ names vars then [
    Spec.Ecdsa.Rfc6979.Curves.p384SignApi.artifact PPC64LE.target {
      tables := [("hmac", tables vars)]
      code := signCodeT (p384R hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.p384.tries vars
      stack := stackT
      verified := p384T_verified hasLaw.law vars hv }]
  else [])

end VG.Artifacts.EcdsaP384.PPC64LE
