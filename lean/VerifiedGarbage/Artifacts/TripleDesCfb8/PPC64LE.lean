module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Cfb8
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesVerified
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesFrame
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Scrub
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES-CFB8 on PPC64LE -/

namespace VG.Artifacts.TripleDesCfb8.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.TripleDes.cfb8EncryptApi.artifact PPC64LE.target {
    code := Impl.TripleDes.PPC64LE.Fn.cfb8Encrypt
    verified := Proof.TripleDes.PPC64LE.Scrub.cfb8Encrypt_scrubbed },
  Spec.TripleDes.cfb8DecryptApi.artifact PPC64LE.target {
    code := Impl.TripleDes.PPC64LE.Fn.cfb8Decrypt
    verified := Proof.TripleDes.PPC64LE.Scrub.cfb8Decrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.TripleDesCfb8.PPC64LE
