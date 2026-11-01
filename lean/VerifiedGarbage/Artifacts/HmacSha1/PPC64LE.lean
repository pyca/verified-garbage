module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha1
public import VerifiedGarbage.Proof.Framework.Registration

/-! # HMAC-SHA-1 (RFC 2104) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.HmacSha1.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.sha1I.initAnyKeyApi.artifact PPC64LE.target {
    code := Proof.Hmac.Stream.PPC64LE.initCode Proof.Hmac.Stream.PPC64LE.Sha1.hash Spec.Hmac.sha1I 6
    stack := 96 + Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha1I
    verified := Proof.Hmac.Stream.PPC64LE.Sha1.initAny },
  Spec.Hmac.sha1I.finalizeApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch (Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha1I) .r7
      Proof.Hmac.Stream.PPC64LE.Sha1.hash.finalize
    stack := 96 + Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha1I
    verified := Proof.Hmac.Stream.PPC64LE.Sha1.finalize }]

end VG.Artifacts.HmacSha1.PPC64LE
