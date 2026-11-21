module

public import VerifiedGarbage.Proof.Ct.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # Constant-time byte comparison on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Ct.PPC64LE

def artifacts : List Artifact := [
  Spec.Ct.eqApi.artifact PPC64LE.target {
    code := Impl.Ct.PPC64LE.Fn.eq
    verified := Proof.Ct.PPC64LE.Scrub.eq_scrubbed }]

end VG.Artifacts.Ct.PPC64LE
