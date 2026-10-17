module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.VfVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.RcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSASSA-PKCS1-v1_5 verification and recovery with a precomputed public key on ARMv7

`vg_rsa_pkcs1_verify_precomputed` and `vg_rsa_pkcs1_recover_precomputed`
call the baseline `vg_rsa_public_precomputed_checked` (ARMv7 has no other
implementation of it). Each uses 2192 bytes of stack: the push of the
registers (56 bytes), its frame (2080 bytes) and the 56 bytes of the
call's.
-/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Sig.Arm

def artifacts : List Artifact := [
  Spec.RsaPkcs1Sig.verifyPrecomputedApi.artifact Arm.target {
    notes := ["Baseline ARMv7. This implementation calls `vg_rsa_public_precomputed_checked` with the \
        cached modulus values into its frame, writes EMSA-PKCS1-v1_5's encoding of `digest` beside the \
        result and compares the two without a branch, and returns the public operation's status masked \
        with the encoding's success and the comparison: nothing after the call branches on its result."]
    code := Impl.RsaPkcs1Sig.Arm.Precomputed.code Proof.RsaPkcs1Sig.Arm.pdBase.name
      Proof.RsaPkcs1Sig.Arm.pdBase.code
    stack := 2192
    verified := Proof.RsaPkcs1Sig.Arm.Vf.code_verified Proof.RsaPkcs1Sig.Arm.pdBase },
  Spec.RsaPkcs1Sig.recoverPrecomputedApi.artifact Arm.target {
    notes := ["Baseline ARMv7. This implementation calls `vg_rsa_public_precomputed_checked` with the \
        cached modulus values into its frame, writes EMSA-PKCS1-v1_5's encoding of the last `out_len` \
        bytes of the result beside it and compares the two, then copies those bytes to `out` and masks \
        them to zeros, and the result to 0, unless the public operation succeeded and the two are equal: \
        nothing after the call branches on its result."]
    code := Impl.RsaPkcs1Sig.Arm.RecoverPrecomputed.code Proof.RsaPkcs1Sig.Arm.pdBase.name
      Proof.RsaPkcs1Sig.Arm.pdBase.code
    stack := 2192
    verified := Proof.RsaPkcs1Sig.Arm.Rc.code_verified Proof.RsaPkcs1Sig.Arm.pdBase }]

end VG.Artifacts.RsaPkcs1Sig.Arm
