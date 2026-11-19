module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # HMAC-SHA-512/256 (RFC 2104) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.HmacSha512_256.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.sha512_256I.initAnyKeyApi.artifact PPC64LE.target Proof.Hmac.Stream.PPC64LE.Scrub.sha512_256InitAnyKeyReg,
  Spec.Hmac.sha512_256I.finalizeApi.artifact PPC64LE.target Proof.Hmac.Stream.PPC64LE.Scrub.sha512_256FinalizeReg]

end VG.Artifacts.HmacSha512_256.PPC64LE
