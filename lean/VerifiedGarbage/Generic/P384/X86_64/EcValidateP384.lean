module

public import VerifiedGarbage.Proof.EcKey.Validate.X86_64.P384
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Standalone P384 public-key validation on x86-64 -/

@[expose] public section

namespace VG.Generic.P384.X86_64.EcValidateP384

open VG.Proof.EcKey.Validate.X86_64.P384

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P384.curve) : List Artifact :=
  [false, true].map fun adx =>
    Spec.EcKey.P384.inst.validatePublicKeyApi.artifact X86_64.target {
      suffix := if adx then "_adx" else ""
      code := code adx
      verified := verified h.inv adx
      stack := 8
      features := if adx then ["bmi2", "adx"] else [] }

end VG.Generic.P384.X86_64.EcValidateP384
