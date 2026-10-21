module

public import VerifiedGarbage.Proof.EcKey.Validate.X86_64.P192
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Standalone P192 public-key validation on x86-64 -/

@[expose] public section

namespace VG.Generic.P192.X86_64.EcValidateP192

open VG.Proof.EcKey.Validate.X86_64.P192

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P192.curve) : List Artifact :=
  [Spec.EcKey.P192.inst.validatePublicKeyApi.artifact X86_64.target {
    code := code false
    verified := verified h.inv false
    stack := 8 }]

end VG.Generic.P192.X86_64.EcValidateP192
