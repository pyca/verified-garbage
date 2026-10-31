module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Sha256
public import VerifiedGarbage.Proof.Framework.Registration

/-! # PBKDF2-HMAC-SHA-256 (RFC 8018) on PPC64LE: the iteration and the whole derivation -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha256.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.sha256I.iterateApi.artifact PPC64LE.target {
    code := Proof.Pbkdf2.PPC64LE.Sha256.code
    verified := Proof.Pbkdf2.PPC64LE.Sha256.iterate },
  Spec.Hmac.sha256I.pbkdf2Api.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch (Proof.Pbkdf2.Whole.PPC64LE.pbkFrame Spec.Hmac.sha256I) .r10
      Proof.Pbkdf2.Whole.PPC64LE.Sha256.F.pbkdf2
    stack := Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha256I + 144 + Proof.Pbkdf2.Whole.PPC64LE.pbkFrame Spec.Hmac.sha256I
    verified := Proof.Pbkdf2.Whole.PPC64LE.Sha256.pbkdf2 },
  -- Scrypt's code calls `pbkdf2` with its own working space.
  Spec.Hmac.sha256I.pbkdf2ScratchApi.artifact PPC64LE.target {
    code := Proof.Pbkdf2.Whole.PPC64LE.Sha256.F.pbkdf2
    stack := Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha256I + 144
    verified := Proof.Pbkdf2.Whole.PPC64LE.Sha256.scratch }]

end VG.Artifacts.Pbkdf2Sha256.PPC64LE
