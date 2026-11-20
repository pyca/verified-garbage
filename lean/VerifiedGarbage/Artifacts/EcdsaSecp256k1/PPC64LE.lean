module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.PPC64LE
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
public import VerifiedGarbage.Impl.Ecdsa.Verify.Secp256k1.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Secp256k1.Verified
public import VerifiedGarbage.Spec.Ecdsa.Verify.Secp256k1
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Scrub
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Secp256k1.Lit
public import VerifiedGarbage.Proof.Secp256k1.PPC64LE.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Secp256k1
public import VerifiedGarbage.Proof.HmacTable.PPC64LE.Vars
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Secp256k1.CombLit

/-! # ECDSA over secp256k1 (FIPS 186-5) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcdsaSecp256k1.PPC64LE

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (OK)
open VG.Proof.HmacTable.PPC64LE (vars names)

open VG.Proof.Secp256k1.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.Secp256k1.verifyHashApi.artifact PPC64LE.target {
    code := Impl.Ecdsa.Verify.PPC64LE.Fn.secp256k1Verify
    verified := .scrubbed (Proof.Ecdsa.Verify.PPC64LE.Scrub.secp256k1Verify_scrubbed hasLaw.law) }] ++
  (if hv : OK vars ∧ "VG_SECP256K1_COMB" ∉ names vars then [
    Spec.Ecdsa.Rfc6979.Curves.secp256k1SignApi.artifact PPC64LE.target
      (Proof.Ecdsa.Rfc6979.PPC64LE.Scrub.secp256k1Sign hasLaw.law hv)]
  else [])

end VG.Artifacts.EcdsaSecp256k1.PPC64LE
