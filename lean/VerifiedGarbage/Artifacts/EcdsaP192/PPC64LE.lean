module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P192.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P192.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.P192
public import VerifiedGarbage.Impl.Ecdsa.Verify.P192.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P192.Verified
public import VerifiedGarbage.Spec.Ecdsa.Verify.P192
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Scrub
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P192.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P192.Lit
public import VerifiedGarbage.Proof.P192.PPC64LE.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P192
public import VerifiedGarbage.Proof.HmacTable.PPC64LE.Vars

/-! # ECDSA over P-192 (FIPS 186-5) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcdsaP192.PPC64LE

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (OK)
open VG.Proof.HmacTable.PPC64LE (vars)

open VG.Proof.P192.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P192.verifyHashApi.artifact PPC64LE.target
    (Proof.Ecdsa.Verify.PPC64LE.Scrub.p192Verify hasLaw.law)] ++
  (if hv : OK vars then [
    Spec.Ecdsa.Rfc6979.Curves.p192SignApi.artifact PPC64LE.target
      (Proof.Ecdsa.Rfc6979.PPC64LE.Scrub.p192Sign hasLaw.law hv)]
  else [])

end VG.Artifacts.EcdsaP192.PPC64LE
