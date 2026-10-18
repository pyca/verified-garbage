module

public import VerifiedGarbage.Proof.RsaOaep.Arm.EncVerified
public import VerifiedGarbage.Proof.RsaOaep.Arm.EncSat
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha384
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSAES-OAEP encryption with SHA-384, MGF1 with SHA-384 and a precomputed public key on ARMv7

`vg_rsa_oaep_sha384_mgf1_sha384_encrypt_precomputed` calls the baseline
`vg_rsa_public_precomputed_checked` (ARMv7 has no other implementation of
it). It uses 240 bytes of stack: the push of the registers (56 bytes), its
frame (128 bytes) and the 56 bytes of the calls'.
-/

@[expose] public section

namespace VG.Artifacts.RsaOaepSha384Mgf1Sha384.Arm

def artifacts : List Artifact := [
  (Spec.RsaOaep.encryptPrecomputedApi Spec.Mgf1.sha384 Spec.Mgf1.sha384).artifact Arm.target {
    notes := ["Baseline ARMv7. This implementation hashes the label with `vg_sha512_update`, masks `DB` \
        and the seed with MGF1 calling `vg_sha512_update`, and calls `vg_rsa_public_precomputed_checked` \
        with the cached modulus values. The message's length is public; its bytes, the label's and \
        the seed's are only copied, hashed and masked."]
    code := Proof.RsaOaep.Arm.Enc.encryptCode (.ofPss Proof.RsaPss.Arm.sha384) (.ofPss Proof.RsaPss.Arm.sha384)
      Proof.RsaPkcs1Sig.Arm.pdBase
    stack := 240
    verified := Proof.RsaOaep.Arm.Enc.encrypt_verified (.ofPss Proof.RsaPss.Arm.sha384) (.ofPss Proof.RsaPss.Arm.sha384)
      (Proof.RsaOaep.Arm.Enc.encrypt_sat_sha384 _) Proof.RsaPkcs1Sig.Arm.pdBase }]

end VG.Artifacts.RsaOaepSha384Mgf1Sha384.Arm
