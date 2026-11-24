module

public import VerifiedGarbage.Proof.TripleDes.X86.Scrub
public import VerifiedGarbage.Impl.TripleDes.X86.Fn
public import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Verified
public import VerifiedGarbage.Impl.TripleDes.X86.Ssse3
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Lit
import VerifiedGarbage.Proof.TripleDes.X86.FbLit

/-! # Triple DES-CFB8 on x86 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb8.X86

def artifacts : List (Artifact X86.target) := [
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

end VG.Artifacts.TripleDesCfb8.X86
