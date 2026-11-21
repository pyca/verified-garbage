module

public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Scrub
public import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE.Fn
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # HMAC-SHA-384 (RFC 2104) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.HmacSha384.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.sha384I.initAnyKeyApi.artifact PPC64LE.target {
    code := Impl.Hmac.Stream.PPC64LE.Fn.initSha384
    verified := Proof.Hmac.Stream.PPC64LE.Scrub.sha384_init_scrubbed },
  Spec.Hmac.sha384I.finalizeApi.artifact PPC64LE.target {
    code := Impl.Hmac.Stream.PPC64LE.Fn.finalizeSha384
    verified := Proof.Hmac.Stream.PPC64LE.Scrub.sha384_finalize_scrubbed }]

end VG.Artifacts.HmacSha384.PPC64LE
