module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # HMAC-SHA-512/224 (RFC 2104) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.HmacSha512_224.PPC64LE

def artifacts : List Artifact := [
  Spec.Hmac.sha512_224I.initAnyKeyApi.artifact PPC64LE.target Proof.Hmac.Stream.PPC64LE.Scrub.sha512_224InitAnyKeyReg,
  Spec.Hmac.sha512_224I.finalizeApi.artifact PPC64LE.target Proof.Hmac.Stream.PPC64LE.Scrub.sha512_224FinalizeReg]

end VG.Artifacts.HmacSha512_224.PPC64LE
