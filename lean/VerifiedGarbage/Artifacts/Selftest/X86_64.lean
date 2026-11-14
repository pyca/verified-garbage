module

public import VerifiedGarbage.Proof.Selftest.X86_64
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.TCB.Registration

/-! # The emitter's self-test on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Selftest.X86_64

def artifacts : List Artifact := [
  { Spec.Selftest.addApi with
    target := .of X86_64.target
    doc := Spec.Selftest.addApi.summary
    code := Proof.Selftest.X86_64.addScrubbed
    contract := Spec.Selftest.addContract X86_64.abi
    verified := Proof.Selftest.X86_64.addScrubbed_verified
    residue := some ⟨Proof.Selftest.X86_64.addScrubbed_noResidue⟩ }]

end VG.Artifacts.Selftest.X86_64
