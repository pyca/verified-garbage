module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # HMAC-MD5 (RFC 2104) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.HmacMd5.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.md5I.initAnyKeyApi.artifact PPC64LE.target Proof.Hmac.Stream.PPC64LE.Scrub.md5InitAnyKeyReg,
  Spec.Hmac.md5I.finalizeApi.artifact PPC64LE.target Proof.Hmac.Stream.PPC64LE.Scrub.md5FinalizeReg]

end VG.Artifacts.HmacMd5.PPC64LE
