module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha224
public import VerifiedGarbage.Proof.Framework.Registration

/-! # HMAC-SHA-224 (RFC 2104) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.HmacSha224.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.sha224I.initAnyKeyApi.artifact PPC64LE.target {
    code := Proof.Hmac.Stream.PPC64LE.initCode Proof.Hmac.Stream.PPC64LE.Sha224.hash Spec.Hmac.sha224I 6
    stack := 96 + Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha224I
    verified := Proof.Hmac.Stream.PPC64LE.Sha224.initAny },
  Spec.Hmac.sha224I.finalizeApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch (Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha224I) .r7
      Proof.Hmac.Stream.PPC64LE.Sha224.hash.finalize
    stack := 96 + Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha224I
    verified := Proof.Hmac.Stream.PPC64LE.Sha224.finalize }]

end VG.Artifacts.HmacSha224.PPC64LE
