module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.X86.Hashes.Sha512
public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Verified
public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Sat

/-!
# RSAES-OAEP with SHA-512/256 and MGF1 with SHA-512/256 on x86: decryption, for each implementation of the CRT

A generic file (see `TCB/Emit.lean`): `vg_rsa_oaep_sha512_256_mgf1_sha512_256_decrypt`, calling
`vg_rsa_private_checked` over an implementation `c` of `vg_rsa_private_crt`
(`Variants/RsaPrivateCrt/X86/`), is emitted once for each, named with its
suffix, and needs its CPU features.

It uses 3552 bytes of stack: the push of the registers (16 bytes), its
frame (144 bytes) and the 3392 bytes of `vg_rsa_private_checked`'s, which
are more than the hash functions' calls use.
-/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.X86.RsaOaepSha512_256Mgf1Sha512_256

open VG.Proof.Rsa.X86.PrivChecked (CrtImpl)

def artifacts (c : CrtImpl) : List Artifact := [
  (Spec.RsaOaep.decryptApi Spec.Mgf1.sha512_256 Spec.Mgf1.sha512_256).artifact X86.target {
    suffix := c.suffix
    notes := ["This implementation calls `" ++ Proof.RsaOaep.X86.Dec.privName c ++ "`, hashes the label with \
      `vg_sha512_update` and unmasks the seed and `DB` with MGF1 calling `vg_sha512_update`. The checks of `Y`, \
      `lHash'` and the separator, the scan for it and the shift of the message to the start of `out` \
      are masks computed without branches, reading every byte of `EM` whatever the outcome; only the \
      lengths and the public key decide a branch or an address."]
    code := Proof.RsaOaep.X86.Dec.decCode Proof.RsaOaep.X86.sha512_256 Proof.RsaOaep.X86.sha512_256 c
    stack := Proof.RsaOaep.X86.Dec.stackBytes
    verified := Proof.RsaOaep.X86.Dec.dec_verified Proof.RsaOaep.X86.sha512_256 Proof.RsaOaep.X86.sha512_256 (Proof.RsaOaep.X86.Dec.dec_sat _ _) c
    spSafe := Proof.RsaOaep.X86.Dec.code_sp Proof.RsaOaep.X86.sha512_256 Proof.RsaOaep.X86.sha512_256 c
    features := c.features }]

end VG.Generic.RsaPrivateCrt.X86.RsaOaepSha512_256Mgf1Sha512_256
