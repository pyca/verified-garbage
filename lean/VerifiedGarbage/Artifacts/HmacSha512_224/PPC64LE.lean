module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512_224
public import VerifiedGarbage.Proof.Framework.Registration

/-! # HMAC-SHA-512/224 (RFC 2104) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.HmacSha512_224.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.sha512_224I.initAnyKeyApi.artifact PPC64LE.target {
    code := Proof.Hmac.Stream.PPC64LE.initCode Proof.Hmac.Stream.PPC64LE.Sha512_224.hash Spec.Hmac.sha512_224I 7
    stack := 96 + Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha512_224I
    verified := Proof.Hmac.Stream.PPC64LE.Sha512_224.initAny },
  Spec.Hmac.sha512_224I.finalizeApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch (Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha512_224I) .r7
      Proof.Hmac.Stream.PPC64LE.Sha512_224.hash.finalize
    stack := 96 + Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha512_224I
    verified := Proof.Hmac.Stream.PPC64LE.Sha512_224.finalize }]

end VG.Artifacts.HmacSha512_224.PPC64LE
