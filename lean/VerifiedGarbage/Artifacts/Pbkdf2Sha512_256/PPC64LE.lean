module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Sha512_256
public import VerifiedGarbage.Proof.Framework.Registration

/-! # PBKDF2-HMAC-SHA-512/256 (RFC 8018) on PPC64LE: the iteration and the whole derivation -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha512_256.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.sha512_256I.pbkdf2Api.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch (Proof.Pbkdf2.Whole.PPC64LE.pbkFrame Spec.Hmac.sha512_256I) .r10
      Proof.Pbkdf2.Whole.PPC64LE.Sha512_256.F.pbkdf2
    stack := Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha512_256I + 144 + Proof.Pbkdf2.Whole.PPC64LE.pbkFrame Spec.Hmac.sha512_256I
    verified := Proof.Pbkdf2.Whole.PPC64LE.Sha512_256.pbkdf2 }]

end VG.Artifacts.Pbkdf2Sha512_256.PPC64LE
