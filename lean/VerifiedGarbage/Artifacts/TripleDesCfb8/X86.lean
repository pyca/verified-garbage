module

public import VerifiedGarbage.Proof.TripleDes.X86.Scrub
public import VerifiedGarbage.Impl.TripleDes.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.TripleDes.X86.FbLit

/-! # Triple DES-CFB8 on x86 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb8.X86

def artifacts : List Artifact := [
  Spec.TripleDes.cfb8EncryptApi.artifact X86.target {
    code := Impl.TripleDes.X86.Fn.cfb8Encrypt
    verified := .scrubbed Proof.TripleDes.X86.Scrub.cfb8Encrypt_scrubbed },
  Spec.TripleDes.cfb8DecryptApi.artifact X86.target {
    code := Impl.TripleDes.X86.Fn.cfb8Decrypt
    verified := .scrubbed Proof.TripleDes.X86.Scrub.cfb8Decrypt_scrubbed }]

end VG.Artifacts.TripleDesCfb8.X86
