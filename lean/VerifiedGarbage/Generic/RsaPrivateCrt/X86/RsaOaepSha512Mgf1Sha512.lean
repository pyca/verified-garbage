module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.X86.Hashes.Sha512
public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Verified
public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Sat

/-!
# RSAES-OAEP with SHA-512 and MGF1 with SHA-512 on x86: decryption, for each implementation of the CRT

A generic file (see `TCB/Emit.lean`): `vg_rsa_oaep_sha512_mgf1_sha512_decrypt`, calling
`vg_rsa_private_checked` over an implementation `c` of `vg_rsa_private_crt`
(`Variants/RsaPrivateCrt/X86/`), is emitted once for each, named with its
suffix, and needs its CPU features.

It uses 3552 bytes of stack: the push of the registers (16 bytes), its
frame (144 bytes) and the 3392 bytes of `vg_rsa_private_checked`'s, which
are more than the hash functions' calls use.
-/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.X86.RsaOaepSha512Mgf1Sha512

open VG.Proof.Rsa.X86.PrivChecked (CrtImpl)

def artifacts (c : CrtImpl) : List Artifact := [
  (Spec.RsaOaep.decryptApi Spec.Mgf1.sha512 Spec.Mgf1.sha512).artifact X86.target {
    suffix := c.suffix
    notes := ["This implementation calls `" ++ Proof.RsaOaep.X86.Dec.privName c ++ "`, hashes the label with \
      `vg_sha512_update` and unmasks the seed and `DB` with MGF1 calling `vg_sha512_update`. The checks of `Y`, \
      `lHash'` and the separator, the scan for it and the shift of the message to the start of `out` \
      are masks computed without branches, reading every byte of `EM` whatever the outcome; only the \
      lengths and the public key decide a branch or an address."]
    code := Proof.RsaOaep.X86.Dec.decCode Proof.RsaOaep.X86.sha512 Proof.RsaOaep.X86.sha512 c
    stack := Proof.RsaOaep.X86.Dec.stackBytes
    verified := Proof.RsaOaep.X86.Dec.dec_verified Proof.RsaOaep.X86.sha512 Proof.RsaOaep.X86.sha512 (Proof.RsaOaep.X86.Dec.dec_sat _ _) c
    spSafe := Proof.RsaOaep.X86.Dec.code_sp Proof.RsaOaep.X86.sha512 Proof.RsaOaep.X86.sha512 c
    features := c.features }]

end VG.Generic.RsaPrivateCrt.X86.RsaOaepSha512Mgf1Sha512
