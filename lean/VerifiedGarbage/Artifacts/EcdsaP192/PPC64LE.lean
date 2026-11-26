module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.P192
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdsa.P192.PPC64LE
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P192.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Spec.Ecdsa.P192
import VerifiedGarbage.Impl.Ecdsa.Verify.P192.PPC64LE
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P192.Verified
import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Scrub
import VerifiedGarbage.Impl.Ecdsa.Rfc6979.PPC64LE.Fn
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Scrub
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P192.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P192.Lit
import VerifiedGarbage.Proof.P192.PPC64LE.Law
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P192
import VerifiedGarbage.Proof.HmacTable.PPC64LE.Vars
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDSA over P-192 (FIPS 186-5) on PPC64LE -/

namespace VG.Artifacts.EcdsaP192.PPC64LE

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (OK)
open VG.Proof.HmacTable.PPC64LE (vars tables fnsOf names)

open VG.Proof.P192.PPC64LE (hasLaw)

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Ecdsa.P192.verifyHashApi.artifact PPC64LE.target {
    code := Impl.Ecdsa.Verify.PPC64LE.Fn.p192Verify
    verified := Proof.Ecdsa.Verify.PPC64LE.Scrub.p192Verify_scrubbed hasLaw.law }] ++
  (if hv : OK vars ∧ "VG_P192_FRAME_CONSTS" ∉ names vars then [
    Spec.Ecdsa.Rfc6979.Curves.p192SignApi.artifact PPC64LE.target {
      tables := [("hmac", tables vars)]
      code := Impl.Ecdsa.Rfc6979.PPC64LE.Fn.p192 (fnsOf vars)
      verified := Proof.Ecdsa.Rfc6979.PPC64LE.Scrub.p192Sign_scrubbed hasLaw.law hv }]
  else [])

spec_apis artifacts

end VG.Artifacts.EcdsaP192.PPC64LE
