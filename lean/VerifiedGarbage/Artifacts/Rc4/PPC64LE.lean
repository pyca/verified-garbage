module

public import VerifiedGarbage.Proof.Rc4.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Rc4.PPC64LE.Lit

/-! # Raw RC4 on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Rc4.PPC64LE

def artifacts : List Artifact := [
  Spec.Rc4.initApi.artifact PPC64LE.target {
    code := Impl.Rc4.PPC64LE.init
    verified := Proof.Rc4.PPC64LE.init_verified },
  Spec.Rc4.applyApi.artifact PPC64LE.target {
    code := Impl.Rc4.PPC64LE.apply
    verified := Proof.Rc4.PPC64LE.apply_verified }]

end VG.Artifacts.Rc4.PPC64LE
