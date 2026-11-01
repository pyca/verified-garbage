module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Sha512_224
public import VerifiedGarbage.Proof.Framework.Registration

/-! # PBKDF2-HMAC-SHA-512/224 (RFC 8018) on PPC64LE: the iteration and the whole derivation -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha512_224.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.sha512_224I.pbkdf2Api.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch (Proof.Pbkdf2.Whole.PPC64LE.pbkFrame Spec.Hmac.sha512_224I) .r10
      Proof.Pbkdf2.Whole.PPC64LE.Sha512_224.F.pbkdf2
    stack := Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha512_224I + 144 + Proof.Pbkdf2.Whole.PPC64LE.pbkFrame Spec.Hmac.sha512_224I
    verified := Proof.Pbkdf2.Whole.PPC64LE.Sha512_224.pbkdf2 }]

end VG.Artifacts.Pbkdf2Sha512_224.PPC64LE
