module

public import VerifiedGarbage.Proof.Rc4.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Rc4.PPC64LE.Lit

/-! # RC4 on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Rc4.PPC64LE

def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Rc4.initApi.artifact PPC64LE.target {
    code := Impl.Rc4.PPC64LE.Fn.init
    verified := Proof.Rc4.PPC64LE.Scrub.init_scrubbed },
  Spec.Rc4.applyApi.artifact PPC64LE.target {
    code := Impl.Rc4.PPC64LE.Fn.apply
    verified := Proof.Rc4.PPC64LE.Scrub.apply_scrubbed }]

end VG.Artifacts.Rc4.PPC64LE
