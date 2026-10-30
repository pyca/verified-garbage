module

public import VerifiedGarbage.Proof.Idea.PPC64LE.Invert
public import VerifiedGarbage.Proof.Idea.PPC64LE.Key
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.PPC64LE.Lit

/-! # IDEA artifacts on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Idea.PPC64LE

def artifacts : List Artifact := [
  Spec.Idea.expandKeyApi.artifact PPC64LE.target {
    code := Impl.Idea.PPC64LE.expandKey
    verified := Proof.Idea.PPC64LE.expandKey_verified },
  Spec.Idea.invertKeyApi.artifact PPC64LE.target {
    code := Impl.Idea.PPC64LE.invertKey
    verified := Proof.Idea.PPC64LE.invertKey_verified },
  Spec.Idea.ecbApi.artifact PPC64LE.target {
    code := Impl.Idea.PPC64LE.ecb
    verified := Proof.Idea.PPC64LE.ecb_verified }]

end VG.Artifacts.Idea.PPC64LE
