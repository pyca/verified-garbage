module

public import VerifiedGarbage.Proof.RsaPss.X86.VfVerified
public import VerifiedGarbage.Proof.RsaPss.X86.VfSat
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.X86.Hashes.Sha1

/-!
# RSASSA-PSS verification with SHA-1 on x86, for each SHA-1 backend

A generic file (see `TCB/Emit.lean`):
`vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed` hashes with the streaming and
compression functions of a backend `v` (`Variants/Sha1/X86/`), is emitted
once for each, named with its suffix, and needs its CPU features.

It uses 208 bytes of stack: the push of the registers (16 bytes), its frame
(144 bytes) and the 48 bytes of its calls': the hash function's, and the 44
of `vg_rsa_public_precomputed_checked`.
-/

@[expose] public section

namespace VG.Generic.Sha1.X86.RsaPssSha1

def artifacts (v : Proof.Sha1.X86.Variants.Backend) : List Artifact := [
  (Spec.RsaPss.verifyPrecomputedApi Spec.Mgf1.sha1 Spec.Mgf1.sha1).artifact X86.target {
    suffix := v.stream.suffix
    code := Proof.RsaPss.X86.Vf.verifyCode (Proof.RsaPss.X86.sha1 v) Proof.RsaPkcs1Sig.X86.Ver.baseline
    stack := Proof.RsaPss.X86.Vf.stackBytes
    verified := Proof.RsaPss.X86.Vf.verify_verified (Proof.RsaPss.X86.sha1 v) Proof.RsaPss.X86.Vf.verify_sat_sha1
      Proof.RsaPkcs1Sig.X86.Ver.baseline
    spSafe := Proof.RsaPss.X86.Vf.code_sp (Proof.RsaPss.X86.sha1 v) Proof.RsaPkcs1Sig.X86.Ver.baseline
    features := v.features }]

end VG.Generic.Sha1.X86.RsaPssSha1
