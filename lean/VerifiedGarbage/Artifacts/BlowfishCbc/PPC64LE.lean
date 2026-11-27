module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blowfish.Cbc
import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesVerified
import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesFrame
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blowfish.PPC64LE.Scrub
import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Blowfish-CBC on PPC64LE -/

namespace VG.Artifacts.BlowfishCbc.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact PPC64LE.target {
    code := Impl.Blowfish.PPC64LE.Fn.cbcEncryptChained
    verified := Proof.Blowfish.PPC64LE.Scrub.cbcEncryptChained_scrubbed },
  Spec.Blowfish.cbcDecryptChainedApi.artifact PPC64LE.target {
    code := Impl.Blowfish.PPC64LE.Fn.cbcDecryptChained
    verified := Proof.Blowfish.PPC64LE.Scrub.cbcDecryptChained_scrubbed }]

spec_apis artifacts

end VG.Artifacts.BlowfishCbc.PPC64LE
