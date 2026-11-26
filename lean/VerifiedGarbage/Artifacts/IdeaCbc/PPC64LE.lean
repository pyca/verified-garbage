module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Idea.Cbc
import VerifiedGarbage.Proof.Idea.PPC64LE.ModesVerified
import VerifiedGarbage.Proof.Idea.PPC64LE.ModesFrame
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.PPC64LE.Scrub
import VerifiedGarbage.Proof.Idea.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # IDEA-CBC on PPC64LE -/

namespace VG.Artifacts.IdeaCbc.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Idea.cbcEncryptChainedApi.artifact PPC64LE.target {
    code := Impl.Idea.PPC64LE.Fn.cbcEncryptChained
    verified := Proof.Idea.PPC64LE.Scrub.cbcEncryptChained_scrubbed },
  Spec.Idea.cbcDecryptChainedApi.artifact PPC64LE.target {
    code := Impl.Idea.PPC64LE.Fn.cbcDecryptChained
    verified := Proof.Idea.PPC64LE.Scrub.cbcDecryptChained_scrubbed }]

spec_apis artifacts

end VG.Artifacts.IdeaCbc.PPC64LE
