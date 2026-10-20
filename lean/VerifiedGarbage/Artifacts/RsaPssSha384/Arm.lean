module

public import VerifiedGarbage.Proof.RsaPss.Arm.VfVerified
public import VerifiedGarbage.Proof.RsaPss.Arm.VfSat
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha384
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSASSA-PSS verification with SHA-384 and a precomputed public key on ARMv7

`vg_rsa_pss_sha384_mgf1_sha384_verify_precomputed` calls the baseline
`vg_rsa_public_precomputed_checked` (ARMv7 has no other implementation of
it). It uses 240 bytes of stack: the push of the registers (56 bytes), its
frame (128 bytes) and the 56 bytes of the call's.
-/

@[expose] public section

namespace VG.Artifacts.RsaPssSha384.Arm

def artifacts : List Artifact := [
  (Spec.RsaPss.verifyPrecomputedApi Spec.Mgf1.sha384 Spec.Mgf1.sha384).artifact Arm.target {
    notes := ["Baseline ARMv7. This implementation calls `vg_rsa_public_precomputed_checked` with the \
        cached modulus values, then checks EMSA-PSS in its working space without branching on the \
        encoding: `maskedDB` is unmasked with MGF1, and the end of `DB`'s padding is found by a scan \
        of all its bytes. A specified salt length copies that many trailing bytes of `DB` into `M'` \
        and hashes only the blocks it needs; an unknown salt length shifts `DB` into place in ten \
        masked passes and hashes the blocks of the longest salt. Only the lengths, the salt-length \
        mode and the public key decide a branch or an address."]
    code := Proof.RsaPss.Arm.Vf.verifyCode Proof.RsaPss.Arm.sha384 Proof.RsaPkcs1Sig.Arm.pdBase
    stack := 240
    verified := Proof.RsaPss.Arm.Vf.verify_verified Proof.RsaPss.Arm.sha384 Proof.RsaPss.Arm.Vf.verify_sat_sha384
      Proof.RsaPkcs1Sig.Arm.pdBase }]

end VG.Artifacts.RsaPssSha384.Arm
