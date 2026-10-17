module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.PcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSAES-PKCS1-v1_5 encryption (RFC 8017 §7.2.1) on ARMv7

`vg_rsa_pkcs1_encrypt_precomputed` calls the baseline
`vg_rsa_public_precomputed_checked` (ARMv7 has no other implementation of
it). It uses 1168 bytes of stack: the push of the registers (56 bytes), its
frame (1056 bytes) and the 56 bytes of the call's.
-/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Enc.Arm

def artifacts : List Artifact := [
  Spec.RsaPkcs1Enc.encryptPrecomputedApi.artifact Arm.target {
    notes := ["Baseline ARMv7. This implementation builds `EM = 0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M` in its \
        frame, finding whether `PS` has a zero byte without a branch (the top bit of `byte - 1`), and \
        calls `vg_rsa_public_precomputed_checked` on it with the cached modulus values. It then masks \
        `out` and the result with `z - 1` for the zero test `z`, so that they are zeros and 0 if `PS` had \
        a zero byte, without branching on the public operation's result, and overwrites the frame's `EM` \
        with zeros either way."]
    code := Impl.RsaPkcs1Enc.Arm.Precomputed.code Proof.RsaPkcs1Sig.Arm.pdBase.name
      Proof.RsaPkcs1Sig.Arm.pdBase.code
    stack := 1168
    verified := Proof.RsaPkcs1Enc.Arm.Pc.code_verified Proof.RsaPkcs1Sig.Arm.pdBase }]

end VG.Artifacts.RsaPkcs1Enc.Arm
