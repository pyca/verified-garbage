module

public meta import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.PcVerified
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.PcBase
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Precomputed
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Impl.RsaPkcs1Enc.Arm.Precomputed
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
public import VerifiedGarbage.Proof.Rsa.Arm.PublicOfCrt
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.PcVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecVerified

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
    verified := (Proof.RsaPkcs1Enc.Arm.Dec.code_verified v)
    features := v.features },
  Spec.RsaPkcs1Enc.encryptPrecomputedApi.artifact Arm.target {
    suffix := v.suffix
    notes := ["ARMv7 with the selected RSA public implementation. This implementation builds `EM = 0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M` in its \
        frame, finding whether `PS` has a zero byte without a branch (the top bit of `byte - 1`), and \
        calls `vg_rsa_public_precomputed_checked` on it with the cached modulus values. It then masks \
        `out` and the result with `z - 1` for the zero test `z`, so that they are zeros and 0 if `PS` had \
        a zero byte, without branching on the public operation's result, and overwrites the frame's `EM` \
        with zeros either way."]
    code := Impl.RsaPkcs1Enc.Arm.Precomputed.code (Proof.Rsa.Arm.pdOfCrt v).name
      (Proof.Rsa.Arm.pdOfCrt v).code
    stack := 1168
    verified := (Proof.RsaPkcs1Enc.Arm.Pc.code_verified (Proof.Rsa.Arm.pdOfCrt v))
    features := v.features }]

end VG.Generic.RsaPrivateCrt.Arm.RsaPkcs1Enc
