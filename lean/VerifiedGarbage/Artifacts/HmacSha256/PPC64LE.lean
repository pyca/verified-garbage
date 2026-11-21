module

public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Scrub
public import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE.Fn
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # HMAC-SHA-256 (RFC 2104) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.HmacSha256.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.sha256I.initAnyKeyApi.artifact PPC64LE.target {
    code := Impl.Hmac.Stream.PPC64LE.Fn.initSha256
    verified := .scrubbed Proof.Hmac.Stream.PPC64LE.Scrub.sha256_init_scrubbed },
  Spec.Hmac.sha256I.finalizeApi.artifact PPC64LE.target {
    code := Impl.Hmac.Stream.PPC64LE.Fn.finalizeSha256
    verified := .scrubbed Proof.Hmac.Stream.PPC64LE.Scrub.sha256_finalize_scrubbed }]

end VG.Artifacts.HmacSha256.PPC64LE
