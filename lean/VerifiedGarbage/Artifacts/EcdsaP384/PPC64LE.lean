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
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Scrub
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.PPC64LE.Fn
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Scrub
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P384.Lit
public import VerifiedGarbage.Proof.P384.PPC64LE.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P384
public import VerifiedGarbage.Proof.HmacTable.PPC64LE.Vars
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384.CombLit

/-! # ECDSA over P-384 (FIPS 186-5) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcdsaP384.PPC64LE

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (OK)
open VG.Proof.HmacTable.PPC64LE (vars names tables fnsOf)

open VG.Proof.P384.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P384.verifyHashApi.artifact PPC64LE.target {
    code := Impl.Ecdsa.Verify.PPC64LE.Fn.p384Verify
    verified := .scrubbed (Proof.Ecdsa.Verify.PPC64LE.Scrub.p384Verify_scrubbed hasLaw.law) }] ++
  (if hv : OK vars ∧ "VG_P384_COMB" ∉ names vars then [
    Spec.Ecdsa.Rfc6979.Curves.p384SignApi.artifact PPC64LE.target {
      tables := [("hmac", tables vars)]
      code := Impl.Ecdsa.Rfc6979.PPC64LE.Fn.p384 (fnsOf vars)
      verified := .scrubbed (Proof.Ecdsa.Rfc6979.PPC64LE.Scrub.p384Sign_scrubbed hasLaw.law hv) }]
  else [])

end VG.Artifacts.EcdsaP384.PPC64LE
