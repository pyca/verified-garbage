module

public import VerifiedGarbage.Proof.Rsa.AArch64.PrivVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivCT
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivCheckOk
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivCrt
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivRelease
public import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rsa.AArch64.PrivCT
import VerifiedGarbage.Proof.Rsa.AArch64.PrivCheckOk
import VerifiedGarbage.Proof.Rsa.AArch64.PrivCrt
import VerifiedGarbage.Proof.Rsa.AArch64.PrivRelease
import VerifiedGarbage.Proof.Rsa.Octets

/-! # The checked RSA private-key operation on AArch64 -/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.AArch64.Rsa

open VG.Proof.Rsa.AArch64

def artifacts (v : CrtImpl) : List Artifact := [
  Spec.Rsa.privateCheckedApi.artifact AArch64.target {
    suffix := v.suffix
    code := privCode v
    stack := stackBytes
    verified := code_verified v
    features := v.features }]

end VG.Generic.RsaPrivateCrt.AArch64.Rsa
