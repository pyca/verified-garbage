module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.X86.Hashes.Sha224
public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Verified
public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Sat

/-!
# RSAES-OAEP with SHA-224 and MGF1 with SHA-224 on x86: decryption, for each Sha256 backend and implementation of the CRT

A generic file of two interfaces (see `TCB/Emit.lean`):
`vg_rsa_oaep_sha224_mgf1_sha224_decrypt` hashes with the streaming functions of
a Sha256 backend `v` (`Variants/Sha256/X86/`), and calls `vg_rsa_private_checked` over an implementation `c` of
`vg_rsa_private_crt` (`Variants/RsaPrivateCrt/X86/`). It is emitted once for
each combination, named by `Emit.qualifiedName` with the tags `sha256` and `crt`, and needs
their CPU features.

It uses 3552 bytes of stack: the push of the registers (16 bytes), its
frame (144 bytes) and the 3392 bytes of `vg_rsa_private_checked`'s, which
are more than the hash functions' calls use.
-/

@[expose] public section

namespace VG.Generic.Sha256.RsaPrivateCrt.X86.RsaOaepSha224Mgf1Sha224

open VG.Proof.Rsa.X86.PrivChecked (CrtImpl)

def artifacts (v : Proof.Sha256.X86.Variants.Backend) (c : CrtImpl) : List Artifact := [
  (Spec.RsaOaep.decryptApi Spec.Mgf1.sha224 Spec.Mgf1.sha224).artifact X86.target {
    suffix := Emit.qualifiedName "" [("sha256", v.stream.suffix), ("crt", c.suffix)]
    notes := ["This implementation calls `" ++ Proof.RsaOaep.X86.Dec.privName c ++ "`, hashes the label with \
      `vg_sha256_update` and unmasks the seed and `DB` with MGF1 calling `vg_sha256_update`. The checks of `Y`, \
      `lHash'` and the separator, the scan for it and the shift of the message to the start of `out` \
      are masks computed without branches, reading every byte of `EM` whatever the outcome; only the \
      lengths and the public key decide a branch or an address."]
    code := Proof.RsaOaep.X86.Dec.decCode (Proof.RsaOaep.X86.sha224 v) (Proof.RsaOaep.X86.sha224 v) c
    stack := Proof.RsaOaep.X86.Dec.stackBytes
    verified := Proof.RsaOaep.X86.Dec.dec_verified (Proof.RsaOaep.X86.sha224 v) (Proof.RsaOaep.X86.sha224 v) (Proof.RsaOaep.X86.Dec.dec_sat _ _) c
    spSafe := Proof.RsaOaep.X86.Dec.code_sp (Proof.RsaOaep.X86.sha224 v) (Proof.RsaOaep.X86.sha224 v) c
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.Sha256.RsaPrivateCrt.X86.RsaOaepSha224Mgf1Sha224
