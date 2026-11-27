module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Cfb8
import VerifiedGarbage.Proof.TripleDes.X86.Scrub
import VerifiedGarbage.Impl.TripleDes.X86.Fn
import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Verified
import VerifiedGarbage.Impl.TripleDes.X86.Ssse3
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Lit
import VerifiedGarbage.Proof.TripleDes.X86.FbLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES-CFB8 on x86 -/

namespace VG.Artifacts.TripleDesCfb8.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.TripleDes.cfb8EncryptApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.TripleDes.X86.Ssse3.Fn.cfb8Encrypt
    verified := Proof.TripleDes.X86.Ssse3.cfb8Encrypt_scrubbed },
  Spec.TripleDes.cfb8EncryptApi.artifact X86.target {
    code := Impl.TripleDes.X86.Fn.cfb8Encrypt
    verified := Proof.TripleDes.X86.Scrub.cfb8Encrypt_scrubbed },
  Spec.TripleDes.cfb8DecryptApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.TripleDes.X86.Ssse3.Fn.cfb8Decrypt
    verified := Proof.TripleDes.X86.Ssse3.cfb8Decrypt_scrubbed },
  Spec.TripleDes.cfb8DecryptApi.artifact X86.target {
    code := Impl.TripleDes.X86.Fn.cfb8Decrypt
    verified := Proof.TripleDes.X86.Scrub.cfb8Decrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.TripleDesCfb8.X86
