module

public import VerifiedGarbage.Proof.EcKey.Validate.X86_64.BrainpoolP256r1
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Standalone BrainpoolP256r1 public-key validation on x86-64 -/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.X86_64.EcValidateBrainpoolP256r1

open VG.Proof.EcKey.Validate.X86_64.BrainpoolP256r1

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.BrainpoolP256r1.curve) : List Artifact :=
  [Spec.EcKey.BrainpoolP256r1.inst.validatePublicKeyApi.artifact X86_64.target {
    code := code false
    verified := verified h.inv false
    stack := 8 }]

end VG.Generic.BrainpoolP256r1.X86_64.EcValidateBrainpoolP256r1
