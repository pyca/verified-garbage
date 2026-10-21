module

public import VerifiedGarbage.Proof.EcKey.Validate.X86_64.P256
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Standalone P256 public-key validation on x86-64 -/

@[expose] public section

namespace VG.Generic.P256.X86_64.EcValidateP256

open VG.Proof.EcKey.Validate.X86_64.P256

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P256.curve) : List Artifact :=
  [false, true].map fun adx =>
    Spec.EcKey.P256.inst.validatePublicKeyApi.artifact X86_64.target {
      suffix := if adx then "_adx" else ""
      code := code adx
      verified := verified h.inv adx
      stack := 8
      features := if adx then ["bmi2", "adx"] else [] }

end VG.Generic.P256.X86_64.EcValidateP256
