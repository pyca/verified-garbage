module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # HMAC-SHA-224 (RFC 2104) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.HmacSha224.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.sha224I.initAnyKeyApi.artifact PPC64LE.target Proof.Hmac.Stream.PPC64LE.Scrub.sha224InitAnyKeyReg,
  Spec.Hmac.sha224I.finalizeApi.artifact PPC64LE.target Proof.Hmac.Stream.PPC64LE.Scrub.sha224FinalizeReg]

end VG.Artifacts.HmacSha224.PPC64LE
