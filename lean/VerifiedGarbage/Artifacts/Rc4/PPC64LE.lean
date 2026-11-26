module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Rc4.Contract
import VerifiedGarbage.Proof.Rc4.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Rc4.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RC4 on PPC64LE -/

namespace VG.Artifacts.Rc4.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Rc4.initApi.artifact PPC64LE.target {
    code := Impl.Rc4.PPC64LE.Fn.init
    verified := Proof.Rc4.PPC64LE.Scrub.init_scrubbed },
  Spec.Rc4.applyApi.artifact PPC64LE.target {
    code := Impl.Rc4.PPC64LE.Fn.apply
    verified := Proof.Rc4.PPC64LE.Scrub.apply_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Rc4.PPC64LE
