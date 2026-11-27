module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Contract
import VerifiedGarbage.Proof.TripleDes.X86.Scrub
import VerifiedGarbage.Impl.TripleDes.X86.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES on x86 -/

namespace VG.Artifacts.TripleDes.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.TripleDes.expandKeyApi.artifact X86.target {
    code := Impl.TripleDes.X86.Fn.expandKey
    verified := Proof.TripleDes.X86.Scrub.expandKey_scrubbed },
  Spec.TripleDes.ecbEncryptApi.artifact X86.target {
    code := Impl.TripleDes.X86.Fn.ecbEncrypt
    verified := Proof.TripleDes.X86.Scrub.ecbEncrypt_scrubbed },
  Spec.TripleDes.ecbDecryptApi.artifact X86.target {
    code := Impl.TripleDes.X86.Fn.ecbDecrypt
    verified := Proof.TripleDes.X86.Scrub.ecbDecrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.TripleDes.X86
