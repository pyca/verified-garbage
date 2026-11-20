module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Scrub
public import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE.Fn
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # PBKDF2-HMAC-SHA-224 (RFC 8018) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha224.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.sha224I.pbkdf2Api.artifact PPC64LE.target {
    code := Impl.Pbkdf2.Whole.PPC64LE.Fn.sha224
    verified := .scrubbed Proof.Pbkdf2.Whole.PPC64LE.Scrub.sha224_scrubbed }]

end VG.Artifacts.Pbkdf2Sha224.PPC64LE
