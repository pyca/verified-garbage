module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # HMAC-SHA-1 (RFC 2104) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.HmacSha1.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.sha1I.initAnyKeyApi.artifact PPC64LE.target Proof.Hmac.Stream.PPC64LE.Scrub.sha1InitAnyKeyReg,
  Spec.Hmac.sha1I.finalizeApi.artifact PPC64LE.target Proof.Hmac.Stream.PPC64LE.Scrub.sha1FinalizeReg]

end VG.Artifacts.HmacSha1.PPC64LE
