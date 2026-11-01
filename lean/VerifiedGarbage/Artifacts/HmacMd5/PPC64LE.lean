module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Md5
public import VerifiedGarbage.Proof.Framework.Registration

/-! # HMAC-MD5 (RFC 2104) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.HmacMd5.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.md5I.initAnyKeyApi.artifact PPC64LE.target {
    code := Proof.Hmac.Stream.PPC64LE.initCode Proof.Hmac.Stream.PPC64LE.Md5.hash Spec.Hmac.md5I 6
    stack := 96 + Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.md5I
    verified := Proof.Hmac.Stream.PPC64LE.Md5.initAny },
  Spec.Hmac.md5I.finalizeApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch (Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.md5I) .r7
      Proof.Hmac.Stream.PPC64LE.Md5.hash.finalize
    stack := 96 + Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.md5I
    verified := Proof.Hmac.Stream.PPC64LE.Md5.finalize }]

end VG.Artifacts.HmacMd5.PPC64LE
