module

public import VerifiedGarbage.Proof.Ffdh.X86.CheckDomainVerified
public import VerifiedGarbage.Proof.Ffdh.X86.Shape
public import VerifiedGarbage.Proof.Framework.Registration

/-! FFDH's domain and key checks and exchange on baseline i686. -/

@[expose] public section

namespace VG.Artifacts.Ffdh.X86
open VG

def artifacts : List Artifact := [
  Spec.Ffdh.checkDomainApi.artifact X86.target {
    notes := ["Runs on private CRT RSA's operations at a run-time width, at p's width, reading \
      their arguments from a frame of synthetic arguments; every Montgomery multiplication calls \
      `vg_rsa_mont_mul_at`. The subgroup check is a fixed four-bit-window power. The domain's \
      bytes choose the branches. Callee-saved registers reside in scratch."]
    code := Impl.Ffdh.X86.CheckDomain.code
    verified := Proof.Ffdh.X86.CheckDomain.verified
    spSafe := Proof.Ffdh.X86.Shape.checkDomain_spSafe
    stack := 116 }]

end VG.Artifacts.Ffdh.X86
