module

public import VerifiedGarbage.Proof.RsaOaep.Arm.DecVerified
public import VerifiedGarbage.Proof.RsaOaep.Arm.DecSat
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha512_224
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSAES-OAEP decryption with SHA-512/224 and MGF1 with SHA-512/224 on ARMv7, for each implementation of the CRT

A generic file (see `TCB/Emit.lean`): `vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt`, calling
`vg_rsa_private_checked` over an implementation `v` of `vg_rsa_private_crt`
(`Variants/RsaPrivateCrt/Arm/`), is emitted once for each, named with its
suffix, and needs its CPU features.

It uses 3624 bytes of stack: the push of the registers (56 bytes), its
frame (128 bytes) and the 3440 bytes of the call's.
-/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.Arm.RsaOaepSha512_224Mgf1Sha512_224

open VG.Proof.Rsa.Arm (CrtImpl)

def artifacts (v : CrtImpl) : List Artifact := [
  (Spec.RsaOaep.decryptApi Spec.Mgf1.sha512_224 Spec.Mgf1.sha512_224).artifact Arm.target {
    suffix := v.suffix
    notes := ["This implementation calls `" ++ Proof.Rsa.Arm.privName v ++ "`, hashes the label with \
      `vg_sha512_update` and unmasks the seed and `DB` with MGF1 calling `vg_sha512_update`. The checks of `Y`, \
      `lHash'` and the separator, the scan for it and the shift of the message to the start of `out` \
      are masks computed without branches, reading every byte of `EM` whatever the outcome; only the \
      lengths and the public key decide a branch or an address."]
    code := Proof.RsaOaep.Arm.Dec.decCode (.ofPss Proof.RsaPss.Arm.sha512_224) (.ofPss Proof.RsaPss.Arm.sha512_224) v
    stack := 3624
    verified := Proof.RsaOaep.Arm.Dec.dec_verified (.ofPss Proof.RsaPss.Arm.sha512_224) (.ofPss Proof.RsaPss.Arm.sha512_224)
      (Proof.RsaOaep.Arm.Dec.dec_sat _ _) v
    features := v.features }]

end VG.Generic.RsaPrivateCrt.Arm.RsaOaepSha512_224Mgf1Sha512_224
