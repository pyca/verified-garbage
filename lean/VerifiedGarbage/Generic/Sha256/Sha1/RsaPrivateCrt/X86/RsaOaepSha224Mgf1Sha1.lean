module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.X86.Hashes.Sha1
public import VerifiedGarbage.Proof.RsaOaep.X86.Hashes.Sha224
public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Verified
public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Sat

/-!
# RSAES-OAEP with SHA-224 and MGF1 with SHA-1 on x86: decryption, for each Sha256 backend, Sha1 backend and implementation of the CRT

A generic file of three interfaces (see `TCB/Emit.lean`):
`vg_rsa_oaep_sha224_mgf1_sha1_decrypt` hashes with the streaming functions of
a Sha256 backend `v` (`Variants/Sha256/X86/`) and a Sha1 backend `w` (`Variants/Sha1/X86/`), and calls `vg_rsa_private_checked` over an implementation `c` of
`vg_rsa_private_crt` (`Variants/RsaPrivateCrt/X86/`). It is emitted once for
each combination, named by `Emit.qualifiedName` with the tags `sha256`, `sha1` and `crt`, and needs
their CPU features.

It uses 3552 bytes of stack: the push of the registers (16 bytes), its
frame (144 bytes) and the 3392 bytes of `vg_rsa_private_checked`'s, which
are more than the hash functions' calls use.
-/

@[expose] public section

namespace VG.Generic.Sha256.Sha1.RsaPrivateCrt.X86.RsaOaepSha224Mgf1Sha1

open VG.Proof.Rsa.X86.PrivChecked (CrtImpl)

def artifacts (v : Proof.Sha256.X86.Variants.Backend) (w : Proof.Sha1.X86.Variants.Backend) (c : CrtImpl) : List Artifact := [
  (Spec.RsaOaep.decryptApi Spec.Mgf1.sha224 Spec.Mgf1.sha1).artifact X86.target {
    suffix := Emit.qualifiedName "" [("sha256", v.stream.suffix), ("sha1", w.stream.suffix), ("crt", c.suffix)]
    code := Proof.RsaOaep.X86.Dec.decCode (Proof.RsaOaep.X86.sha224 v) (Proof.RsaOaep.X86.sha1 w) c
    stack := Proof.RsaOaep.X86.Dec.stackBytes
    verified := Proof.RsaOaep.X86.Dec.dec_verified (Proof.RsaOaep.X86.sha224 v) (Proof.RsaOaep.X86.sha1 w) (Proof.RsaOaep.X86.Dec.dec_sat _ _) c
    spSafe := Proof.RsaOaep.X86.Dec.code_sp (Proof.RsaOaep.X86.sha224 v) (Proof.RsaOaep.X86.sha1 w) c
    features := (v.features ++ w.features.filter (!v.features.contains ·)) ++
      c.features.filter (!(v.features ++ w.features).contains ·) }]

end VG.Generic.Sha256.Sha1.RsaPrivateCrt.X86.RsaOaepSha224Mgf1Sha1
