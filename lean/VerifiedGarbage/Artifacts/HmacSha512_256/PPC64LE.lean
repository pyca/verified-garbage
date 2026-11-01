module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512_256
public import VerifiedGarbage.Proof.Framework.Registration

/-! # HMAC-SHA-512/256 (RFC 2104) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.HmacSha512_256.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.sha512_256I.initAnyKeyApi.artifact PPC64LE.target {
    code := Proof.Hmac.Stream.PPC64LE.initCode Proof.Hmac.Stream.PPC64LE.Sha512_256.hash Spec.Hmac.sha512_256I 7
    stack := 96 + Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha512_256I
    verified := Proof.Hmac.Stream.PPC64LE.Sha512_256.initAny },
  Spec.Hmac.sha512_256I.finalizeApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch (Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha512_256I) .r7
      Proof.Hmac.Stream.PPC64LE.Sha512_256.hash.finalize
    stack := 96 + Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha512_256I
    verified := Proof.Hmac.Stream.PPC64LE.Sha512_256.finalize }]

end VG.Artifacts.HmacSha512_256.PPC64LE
