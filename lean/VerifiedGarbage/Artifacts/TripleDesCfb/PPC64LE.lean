module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Cfb
public import VerifiedGarbage.Spec.TripleDes.CfbFinal
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesVerified
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesFrame
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FbFinalVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Scrub
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES-CFB64 on PPC64LE -/

namespace VG.Artifacts.TripleDesCfb.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.TripleDes.cfbEncryptApi.artifact PPC64LE.target {
    code := Impl.TripleDes.PPC64LE.Fn.cfbEncrypt
    verified := Proof.TripleDes.PPC64LE.Scrub.cfbEncrypt_scrubbed },
  Spec.TripleDes.cfbDecryptApi.artifact PPC64LE.target {
    code := Impl.TripleDes.PPC64LE.Fn.cfbDecrypt
    verified := Proof.TripleDes.PPC64LE.Scrub.cfbDecrypt_scrubbed },
  Spec.TripleDes.cfbEncryptFinalApi.artifact PPC64LE.target {
    code := Impl.TripleDes.PPC64LE.Fn.cfbEncryptFinal
    verified := Proof.TripleDes.PPC64LE.Scrub.cfbEncryptFinal_scrubbed },
  Spec.TripleDes.cfbDecryptFinalApi.artifact PPC64LE.target {
    code := Impl.TripleDes.PPC64LE.Fn.cfbDecryptFinal
    verified := Proof.TripleDes.PPC64LE.Scrub.cfbDecryptFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.TripleDesCfb.PPC64LE
