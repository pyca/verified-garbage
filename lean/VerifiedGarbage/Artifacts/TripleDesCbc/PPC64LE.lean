module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Cbc
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesVerified
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesFrame
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Scrub
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES-CBC on PPC64LE -/

namespace VG.Artifacts.TripleDesCbc.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact PPC64LE.target {
    code := Impl.TripleDes.PPC64LE.Fn.cbcEncryptChained
    verified := Proof.TripleDes.PPC64LE.Scrub.cbcEncryptChained_scrubbed },
  Spec.TripleDes.cbcDecryptChainedApi.artifact PPC64LE.target {
    code := Impl.TripleDes.PPC64LE.Fn.cbcDecryptChained
    verified := Proof.TripleDes.PPC64LE.Scrub.cbcDecryptChained_scrubbed }]

spec_apis artifacts

end VG.Artifacts.TripleDesCbc.PPC64LE
