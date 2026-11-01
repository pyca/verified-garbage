module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P256.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Verified
public import VerifiedGarbage.Spec.Ecdsa.Verify.P256
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Lit

/-! # ECDSA over P-256 (FIPS 186-5) on PPC64LE -/

@[expose] public section

namespace VG.Generic.P256.PPC64LE.EcdsaP256

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.Ecdsa.P256.verifyApi.artifact PPC64LE.target {
    code := Impl.Ecdsa.Verify.PPC64LE.verifyP256
    verified := Proof.Ecdsa.Verify.PPC64LE.verify_verified h.law }]

end VG.Generic.P256.PPC64LE.EcdsaP256
