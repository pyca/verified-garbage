module

public import VerifiedGarbage.Proof.RsaOaep.Arm.EncVerified
public import VerifiedGarbage.Proof.RsaOaep.Arm.EncSat
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha224
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSAES-OAEP encryption with SHA-224, MGF1 with SHA-224 and a precomputed public key on ARMv7

`vg_rsa_oaep_sha224_mgf1_sha224_encrypt_precomputed` calls the baseline
`vg_rsa_public_precomputed_checked` (ARMv7 has no other implementation of
it). It uses 240 bytes of stack: the push of the registers (56 bytes), its
frame (128 bytes) and the 56 bytes of the calls'.
-/

@[expose] public section

namespace VG.Artifacts.RsaOaepSha224Mgf1Sha224.Arm

def artifacts : List Artifact := [
  (Spec.RsaOaep.encryptPrecomputedApi Spec.Mgf1.sha224 Spec.Mgf1.sha224).artifact Arm.target {
    notes := ["Baseline ARMv7. This implementation hashes the label with `vg_sha256_update`, masks `DB` \
        and the seed with MGF1 calling `vg_sha256_update`, and calls `vg_rsa_public_precomputed_checked` \
        with the cached modulus values. The message's length is public; its bytes, the label's and \
        the seed's are only copied, hashed and masked."]
    code := Proof.RsaOaep.Arm.Enc.encryptCode (.ofPss Proof.RsaPss.Arm.sha224) (.ofPss Proof.RsaPss.Arm.sha224)
      Proof.RsaPkcs1Sig.Arm.pdBase
    stack := 240
    verified := Proof.RsaOaep.Arm.Enc.encrypt_verified (.ofPss Proof.RsaPss.Arm.sha224) (.ofPss Proof.RsaPss.Arm.sha224)
      (Proof.RsaOaep.Arm.Enc.encrypt_sat_sha224 _) Proof.RsaPkcs1Sig.Arm.pdBase }]

end VG.Artifacts.RsaOaepSha224Mgf1Sha224.Arm
