module

public import VerifiedGarbage.Proof.EcKey.Validate.X86_64.P256
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.P256.X86_64.Law

/-! # Standalone P256 public-key validation on x86-64 -/

@[expose] public section

namespace VG.Artifacts.EcValidateP256.X86_64

open VG.Proof.P256.X86_64 (hasLaw)
open VG.Proof.EcKey.Validate.X86_64.P256

def artifacts : List Artifact :=
  [false, true].map fun adx =>
    Spec.EcKey.P256.inst.validatePublicKeyApi.artifact X86_64.target {
      suffix := if adx then "_adx" else ""
      code := code adx
      verified := verified hasLaw.inv adx
      stack := 8
      features := if adx then ["bmi2", "adx"] else [] }

end VG.Artifacts.EcValidateP256.X86_64
