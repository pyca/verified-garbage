module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecVerified

/-!
# RSAES-PKCS1-v1_5 decryption with implicit rejection on x86

A generic file of two interfaces (see `TCB/Emit.lean`):
`vg_rsa_pkcs1_decrypt` calls SHA-256's streaming functions and
HMAC-SHA-256's `init` and `finalize`, made with a SHA-256 backend `v`
(`Variants/Sha256/X86/`), and `vg_rsa_private_checked` calling an
implementation `c` of `vg_rsa_private_crt` (`Variants/RsaPrivateCrt/X86/`).
It is emitted once for each pair, named by `Emit.qualifiedName` with the
tags `sha256` and `crt` (e.g. `vg_rsa_pkcs1_decrypt_sha256_shani`), and
needs both's CPU features.

It uses 3512 bytes of stack: the push of the registers (16 bytes), its
frame (104 bytes) and the 3392 bytes of `vg_rsa_private_checked`'s, which
are more than the hash functions use.
-/

@[expose] public section

namespace VG.Generic.Sha256.RsaPrivateCrt.X86.RsaPkcs1Enc

open VG.Proof.Sha256.X86.Variants (Backend)
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl)

def artifacts (v : Backend) (c : CrtImpl) : List Artifact := [
  Spec.RsaPkcs1Enc.decryptApi.artifact X86.target {
    suffix := Emit.qualifiedName "" [("sha256", v.stream.suffix), ("crt", c.suffix)]
    code := Proof.RsaPkcs1Enc.X86.Dec.decryptCode v c
    stack := Proof.RsaPkcs1Enc.X86.Dec.stackBytes
    verified := Proof.RsaPkcs1Enc.X86.Dec.code_verified v c
    spSafe := Proof.RsaPkcs1Enc.X86.Dec.code_sp v c
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.Sha256.RsaPrivateCrt.X86.RsaPkcs1Enc
