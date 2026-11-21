module

public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Scrub
public import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE.Fn
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # HMAC-SHA-1 (RFC 2104) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.HmacSha1.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.sha1I.initAnyKeyApi.artifact PPC64LE.target {
    code := Impl.Hmac.Stream.PPC64LE.Fn.initSha1
    verified := Proof.Hmac.Stream.PPC64LE.Scrub.sha1_init_scrubbed },
  Spec.Hmac.sha1I.finalizeApi.artifact PPC64LE.target {
    code := Impl.Hmac.Stream.PPC64LE.Fn.finalizeSha1
    verified := Proof.Hmac.Stream.PPC64LE.Scrub.sha1_finalize_scrubbed }]

end VG.Artifacts.HmacSha1.PPC64LE
