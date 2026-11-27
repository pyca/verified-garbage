module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Cfb8
import VerifiedGarbage.Impl.TripleDes.X86_64.Fn
import VerifiedGarbage.Proof.TripleDes.X86_64.FbVerified
import VerifiedGarbage.Proof.TripleDes.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86_64.FbLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES-CFB8 on x86-64 -/

namespace VG.Artifacts.TripleDesCfb8.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.TripleDes.cfb8EncryptApi.artifact X86_64.target { code := Impl.TripleDes.X86_64.Fn.cfb8Encrypt, verified := Proof.TripleDes.X86_64.Scrub.cfb8Encrypt_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.cfb8Encrypt_spSafe },
  Spec.TripleDes.cfb8DecryptApi.artifact X86_64.target { code := Impl.TripleDes.X86_64.Fn.cfb8Decrypt, verified := Proof.TripleDes.X86_64.Scrub.cfb8Decrypt_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.cfb8Decrypt_spSafe }]

spec_apis artifacts

end VG.Artifacts.TripleDesCfb8.X86_64
