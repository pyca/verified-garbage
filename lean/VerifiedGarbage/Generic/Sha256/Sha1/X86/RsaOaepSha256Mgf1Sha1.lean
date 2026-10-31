module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.X86.Hashes.Sha1
public import VerifiedGarbage.Proof.RsaOaep.X86.Hashes.Sha256
public import VerifiedGarbage.Proof.RsaOaep.X86.Enc.Verified
public import VerifiedGarbage.Proof.RsaOaep.X86.Enc.Sat
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances

/-!
# RSAES-OAEP with SHA-256 and MGF1 with SHA-1 on x86: encryption, for each Sha256 backend and Sha1 backend

A generic file of two interfaces (see `TCB/Emit.lean`):
`vg_rsa_oaep_sha256_mgf1_sha1_encrypt_precomputed` hashes the label with the
streaming functions of a Sha256 backend `v` (`Variants/Sha256/X86/`) and
masks with MGF1 over those of a Sha1 backend `w` (`Variants/Sha1/X86/`). It
is emitted once for each pair, named by `Emit.qualifiedName` with the tags
`sha256` and `sha1`, and needs both's CPU features.

It uses 208 bytes of stack: the push of the registers (16 bytes), its frame
(144 bytes) and the 48 bytes of its calls': the hash functions', and the 44
of `vg_rsa_public_precomputed_checked`.
-/

@[expose] public section

namespace VG.Generic.Sha256.Sha1.X86.RsaOaepSha256Mgf1Sha1

def artifacts (v : Proof.Sha256.X86.Variants.Backend) (w : Proof.Sha1.X86.Variants.Backend) : List Artifact := [
  (Spec.RsaOaep.encryptPrecomputedApi Spec.Mgf1.sha256 Spec.Mgf1.sha1).artifact X86.target {
    suffix := Emit.qualifiedName "" [("sha256", v.stream.suffix), ("sha1", w.stream.suffix)]
    code := Proof.RsaOaep.X86.Enc.encryptCode (Proof.RsaOaep.X86.sha256 v) (Proof.RsaOaep.X86.sha1 w) Proof.RsaPkcs1Sig.X86.Ver.baseline
    stack := Proof.RsaOaep.X86.Enc.stackBytes
    verified := Proof.RsaOaep.X86.Enc.encrypt_verified (Proof.RsaOaep.X86.sha256 v) (Proof.RsaOaep.X86.sha1 w)
      (Proof.RsaOaep.X86.Enc.encrypt_sat_sha256 _) Proof.RsaPkcs1Sig.X86.Ver.baseline
    spSafe := Proof.RsaOaep.X86.Enc.code_sp (Proof.RsaOaep.X86.sha256 v) (Proof.RsaOaep.X86.sha1 w) Proof.RsaPkcs1Sig.X86.Ver.baseline
    features := v.features ++ w.features.filter (!v.features.contains ·) }]

end VG.Generic.Sha256.Sha1.X86.RsaOaepSha256Mgf1Sha1
