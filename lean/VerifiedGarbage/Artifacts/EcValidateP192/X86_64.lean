module

public import VerifiedGarbage.Proof.EcKey.Validate.X86_64.P192
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.P192.X86_64.Law

/-! # Standalone P192 public-key validation on x86-64 -/

@[expose] public section

namespace VG.Artifacts.EcValidateP192.X86_64

open VG.Proof.P192.X86_64 (hasLaw)
open VG.Proof.EcKey.Validate.X86_64.P192

def artifacts : List Artifact :=
  [Spec.EcKey.P192.inst.validatePublicKeyApi.artifact X86_64.target {
    code := code false
    verified := verified hasLaw.inv false
    stack := 8 }]

end VG.Artifacts.EcValidateP192.X86_64
