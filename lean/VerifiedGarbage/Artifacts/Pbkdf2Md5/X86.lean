module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Md5
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Instances
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Lit
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Instances
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Sha256.X86.Stream.Variant
import VerifiedGarbage.Proof.Sha256.X86.Stream.Variant

/-! # PBKDF2-HMAC-MD5 (RFC 8018) on x86: the iteration and the whole derivation -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Md5.X86

open VG.Proof.Pbkdf2.Stream.X86

def artifacts : List Artifact := [
  Spec.Hmac.md5I.pbkdf2Api.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Whole.X86.pbkFrame Spec.Hmac.md5I) 7
      Proof.Pbkdf2.Whole.X86.md5F.pbkdf2
    stack := 76 + Proof.Pbkdf2.Whole.X86.pbkFrame Spec.Hmac.md5I
    verified := Proof.Pbkdf2.Whole.X86.pbkFramed Proof.Pbkdf2.Whole.X86.md5
      Proof.Pbkdf2.Whole.X86.md5_pbkFrameSat }]

end VG.Artifacts.Pbkdf2Md5.X86
