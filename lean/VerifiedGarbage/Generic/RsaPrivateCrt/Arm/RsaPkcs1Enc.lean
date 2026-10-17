module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSAES-PKCS1-v1_5 decryption with implicit rejection on ARMv7, for each implementation of the CRT

A generic file (see `TCB/Emit.lean`): `vg_rsa_pkcs1_decrypt`, calling
`vg_rsa_private_checked` over an implementation `v` of `vg_rsa_private_crt`
(`Variants/RsaPrivateCrt/Arm/`), is emitted once for each, named with its
suffix, and needs its CPU features. It calls the ARMv7 SHA-256 and
HMAC-SHA-256 functions (`Artifacts/Sha256/Arm.lean`,
`Artifacts/HmacSha256/Arm.lean`), which have no variants on ARMv7.

It uses 3584 bytes of stack: the push of the registers (56 bytes), its
frame (88 bytes) and the 3440 bytes of `vg_rsa_private_checked`'s, which
are more than the hash functions use.
-/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.Arm.RsaPkcs1Enc

open VG.Proof.Rsa.Arm (CrtImpl)
open VG.Proof.RsaPkcs1Enc.Arm (decFns)

def artifacts (v : CrtImpl) : List Artifact := [
  Spec.RsaPkcs1Enc.decryptApi.artifact Arm.target {
    suffix := v.suffix
    notes := ["This implementation calls `" ++ Proof.Rsa.Arm.privName v ++ "`, then derives `KDK` and the \
      alternative message and lengths with `" ++ decFns.initN ++ "`, `" ++ decFns.updN ++ "`, `" ++
      decFns.finN ++ "`, `" ++ decFns.hiN ++ "` and `" ++ decFns.hfN ++ "`, a block of IRPRF per HMAC. \
      The padding's checks, the scan for the separator, the choice of the alternative length and of the \
      message are masks computed without branches, from the top bit of differences of numbers below \
      2^31, and every byte of `EM` and of the alternative message is read whichever is returned."]
    code := Proof.RsaPkcs1Enc.Arm.Dec.decryptCode v
    stack := 3584
    verified := Proof.RsaPkcs1Enc.Arm.Dec.code_verified v
    features := v.features }]

end VG.Generic.RsaPrivateCrt.Arm.RsaPkcs1Enc
