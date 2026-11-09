module

public import VerifiedGarbage.Proof.EcKey.Validate.X86_64.BrainpoolP256r1
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.BrainpoolP256r1.X86_64.Law

/-! # Standalone BrainpoolP256r1 public-key validation on x86-64 -/

@[expose] public section

namespace VG.Artifacts.EcValidateBrainpoolP256r1.X86_64

open VG.Proof.BrainpoolP256r1.X86_64 (hasLaw)
open VG.Proof.EcKey.Validate.X86_64.BrainpoolP256r1

def artifacts : List Artifact :=
  [Spec.EcKey.BrainpoolP256r1.inst.validatePublicKeyApi.artifact X86_64.target {
    code := code false
    verified := verified hasLaw.inv false
    stack := 8 }]

end VG.Artifacts.EcValidateBrainpoolP256r1.X86_64
