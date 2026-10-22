module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.X86.Hashes.Sha256
public import VerifiedGarbage.Proof.RsaOaep.X86.Enc.Verified
public import VerifiedGarbage.Proof.RsaOaep.X86.Enc.Sat
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances

/-!
# RSAES-OAEP with SHA-256 and MGF1 with SHA-256 on x86: encryption, for each Sha256 backend

A generic file (see `TCB/Emit.lean`):
`vg_rsa_oaep_sha256_mgf1_sha256_encrypt_precomputed` hashes with the streaming and
compression functions of a backend `v` (`Variants/Sha256/X86/`), is emitted
once for each, named with its suffix, and needs its CPU features.

It uses 208 bytes of stack: the push of the registers (16 bytes), its frame
(144 bytes) and the 48 bytes of its calls': the hash functions', and the 44
of `vg_rsa_public_precomputed_checked`.
-/

@[expose] public section

namespace VG.Generic.Sha256.X86.RsaOaepSha256Mgf1Sha256

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  (Spec.RsaOaep.encryptPrecomputedApi Spec.Mgf1.sha256 Spec.Mgf1.sha256).artifact X86.target {
    suffix := v.stream.suffix
    notes := ["This implementation calls `" ++ Proof.RsaPkcs1Sig.X86.Ver.baseline.name ++ "` with the cached modulus \
      values; it hashes the label with `vg_sha256_update`, and masks `DB` and the seed with MGF1 calling \
      `vg_sha256_update`. The message's length is public; its bytes, the label's and the seed's are only \
      copied, hashed and masked."]
    code := Proof.RsaOaep.X86.Enc.encryptCode (Proof.RsaOaep.X86.sha256 v) (Proof.RsaOaep.X86.sha256 v) Proof.RsaPkcs1Sig.X86.Ver.baseline
    stack := Proof.RsaOaep.X86.Enc.stackBytes
    verified := Proof.RsaOaep.X86.Enc.encrypt_verified (Proof.RsaOaep.X86.sha256 v) (Proof.RsaOaep.X86.sha256 v)
      (Proof.RsaOaep.X86.Enc.encrypt_sat_sha256 _) Proof.RsaPkcs1Sig.X86.Ver.baseline
    spSafe := Proof.RsaOaep.X86.Enc.code_sp (Proof.RsaOaep.X86.sha256 v) (Proof.RsaOaep.X86.sha256 v) Proof.RsaPkcs1Sig.X86.Ver.baseline
    features := v.features }]

end VG.Generic.Sha256.X86.RsaOaepSha256Mgf1Sha256
