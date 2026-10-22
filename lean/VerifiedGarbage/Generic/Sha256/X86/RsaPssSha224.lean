module

public import VerifiedGarbage.Proof.RsaPss.X86.VfVerified
public import VerifiedGarbage.Proof.RsaPss.X86.VfSat
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.X86.Hashes.Sha224

/-!
# RSASSA-PSS verification with SHA-224 on x86, for each SHA-256 backend

A generic file (see `TCB/Emit.lean`):
`vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed` hashes with the streaming and
compression functions of a backend `v` (`Variants/Sha256/X86/`), is emitted
once for each, named with its suffix, and needs its CPU features.

It uses 208 bytes of stack: the push of the registers (16 bytes), its frame
(144 bytes) and the 48 bytes of its calls': the hash function's, and the 44
of `vg_rsa_public_precomputed_checked`.
-/

@[expose] public section

namespace VG.Generic.Sha256.X86.RsaPssSha224

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  (Spec.RsaPss.verifyPrecomputedApi Spec.Mgf1.sha224 Spec.Mgf1.sha224).artifact X86.target {
    suffix := v.stream.suffix
    notes := ["This implementation calls `" ++ Proof.RsaPkcs1Sig.X86.Ver.baseline.name ++ "` with the \
      cached modulus values, then checks EMSA-PSS in its working space without branching on the \
      encoding: `maskedDB` is unmasked with MGF1, and the end of `DB`'s padding is found by a scan \
      of all its bytes. A specified salt length copies that many trailing bytes of `DB` into `M'` \
      and hashes only the blocks it needs; an unknown salt length shifts `DB` into place in ten \
      masked passes and hashes the blocks of the longest salt. Only the lengths, the salt-length \
      mode and the public key decide a branch or an address."]
    code := Proof.RsaPss.X86.Vf.verifyCode (Proof.RsaPss.X86.sha224 v) Proof.RsaPkcs1Sig.X86.Ver.baseline
    stack := Proof.RsaPss.X86.Vf.stackBytes
    verified := Proof.RsaPss.X86.Vf.verify_verified (Proof.RsaPss.X86.sha224 v) Proof.RsaPss.X86.Vf.verify_sat_sha224
      Proof.RsaPkcs1Sig.X86.Ver.baseline
    spSafe := Proof.RsaPss.X86.Vf.code_sp (Proof.RsaPss.X86.sha224 v) Proof.RsaPkcs1Sig.X86.Ver.baseline
    features := v.features }]

end VG.Generic.Sha256.X86.RsaPssSha224
