module

public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Scrub
public import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE.Fn
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # HMAC-SHA-512/256 (RFC 2104) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.HmacSha512_256.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.sha512_256I.initAnyKeyApi.artifact PPC64LE.target {
    code := Impl.Hmac.Stream.PPC64LE.Fn.initSha512_256
    verified := Proof.Hmac.Stream.PPC64LE.Scrub.sha512_256_init_scrubbed },
  Spec.Hmac.sha512_256I.finalizeApi.artifact PPC64LE.target {
    code := Impl.Hmac.Stream.PPC64LE.Fn.finalizeSha512_256
    verified := Proof.Hmac.Stream.PPC64LE.Scrub.sha512_256_finalize_scrubbed }]

end VG.Artifacts.HmacSha512_256.PPC64LE
