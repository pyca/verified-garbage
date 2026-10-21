module

public import VerifiedGarbage.Proof.EcKey.Validate.X86_64.Secp256k1
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Standalone Secp256k1 public-key validation on x86-64 -/

@[expose] public section

namespace VG.Generic.Secp256k1.X86_64.EcValidateSecp256k1

open VG.Proof.EcKey.Validate.X86_64.Secp256k1

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.Secp256k1.curve) : List Artifact :=
  [Spec.EcKey.Secp256k1.inst.validatePublicKeyApi.artifact X86_64.target {
    code := code false
    verified := verified h.inv false
    stack := 8 }]

end VG.Generic.Secp256k1.X86_64.EcValidateSecp256k1
