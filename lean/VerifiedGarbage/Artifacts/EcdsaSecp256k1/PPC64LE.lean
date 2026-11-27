module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.Secp256k1
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdsa.Secp256k1.PPC64LE
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Spec.Ecdsa.Secp256k1
import VerifiedGarbage.Impl.Ecdsa.Verify.Secp256k1.PPC64LE
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Secp256k1.Verified
import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Scrub
import VerifiedGarbage.Impl.Ecdsa.Rfc6979.PPC64LE.Fn
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Scrub
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Secp256k1.Lit
import VerifiedGarbage.Proof.Secp256k1.PPC64LE.Law
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Secp256k1
import VerifiedGarbage.Proof.HmacTable.PPC64LE.Vars
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Secp256k1.CombLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDSA over secp256k1 (FIPS 186-5) on PPC64LE -/

namespace VG.Artifacts.EcdsaSecp256k1.PPC64LE

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (OK)
open VG.Proof.HmacTable.PPC64LE (vars names tables fnsOf)

open VG.Proof.Secp256k1.PPC64LE (hasLaw)

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Ecdsa.Secp256k1.verifyHashApi.artifact PPC64LE.target {
    code := Impl.Ecdsa.Verify.PPC64LE.Fn.secp256k1Verify
    verified := Proof.Ecdsa.Verify.PPC64LE.Scrub.secp256k1Verify_scrubbed hasLaw.law }] ++
  (if hv : OK vars ∧ "VG_SECP256K1_COMB" ∉ names vars ∧ "VG_SECP256K1_FRAME_CONSTS" ∉ names vars then [
    Spec.Ecdsa.Rfc6979.Curves.secp256k1SignApi.artifact PPC64LE.target {
      tables := [("hmac", tables vars)]
      code := Impl.Ecdsa.Rfc6979.PPC64LE.Fn.secp256k1 (fnsOf vars)
      verified := Proof.Ecdsa.Rfc6979.PPC64LE.Scrub.secp256k1Sign_scrubbed hasLaw.law hv }]
  else [])

spec_apis artifacts

end VG.Artifacts.EcdsaSecp256k1.PPC64LE
