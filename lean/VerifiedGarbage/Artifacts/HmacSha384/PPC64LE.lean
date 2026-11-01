module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha384
public import VerifiedGarbage.Proof.Framework.Registration

/-! # HMAC-SHA-384 (RFC 2104) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.HmacSha384.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.sha384I.initAnyKeyApi.artifact PPC64LE.target {
    code := Proof.Hmac.Stream.PPC64LE.initCode Proof.Hmac.Stream.PPC64LE.Sha384.hash Spec.Hmac.sha384I 7
    stack := 96 + Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha384I
    verified := Proof.Hmac.Stream.PPC64LE.Sha384.initAny },
  Spec.Hmac.sha384I.finalizeApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch (Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha384I) .r7
      Proof.Hmac.Stream.PPC64LE.Sha384.hash.finalize
    stack := 96 + Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha384I
    verified := Proof.Hmac.Stream.PPC64LE.Sha384.finalize }]

end VG.Artifacts.HmacSha384.PPC64LE
