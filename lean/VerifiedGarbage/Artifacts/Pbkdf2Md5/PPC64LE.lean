module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Md5
public import VerifiedGarbage.Proof.Framework.Registration

/-! # PBKDF2-HMAC-MD5 (RFC 8018) on PPC64LE: the iteration and the whole derivation -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Md5.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.md5I.pbkdf2Api.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch (Proof.Pbkdf2.Whole.PPC64LE.pbkFrame Spec.Hmac.md5I) .r10
      Proof.Pbkdf2.Whole.PPC64LE.Md5.F.pbkdf2
    stack := Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.md5I + 144 + Proof.Pbkdf2.Whole.PPC64LE.pbkFrame Spec.Hmac.md5I
    verified := Proof.Pbkdf2.Whole.PPC64LE.Md5.pbkdf2 }]

end VG.Artifacts.Pbkdf2Md5.PPC64LE
