module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPss.X86.SgVerified
public import VerifiedGarbage.Proof.RsaPss.X86.SgSat
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.X86.Hashes.Sha256

/-!
# RSASSA-PSS signing with SHA-256 on x86, for each SHA-256 backend and implementation of the CRT

A generic file of two interfaces (see `TCB/Emit.lean`):
`vg_rsa_pss_sha256_mgf1_sha256_sign` hashes with the streaming and compression
functions of a backend `v` (`Variants/Sha256/X86/`), and calls
`vg_rsa_private_checked` over an implementation `c` of
`vg_rsa_private_crt` (`Variants/RsaPrivateCrt/X86/`). It is emitted once for
each pair, named by `Emit.qualifiedName` with the tags `sha256` and
`crt`, and needs both's CPU features.

It uses 3552 bytes of stack: the push of the registers (16 bytes), its
frame (144 bytes) and the 3392 bytes of `vg_rsa_private_checked`'s, which
are more than the hash function's calls use.
-/

@[expose] public section

namespace VG.Generic.Sha256.RsaPrivateCrt.X86.RsaPssSha256

open VG.Proof.Rsa.X86.PrivChecked (CrtImpl)

def artifacts (v : Proof.Sha256.X86.Variants.Backend) (c : CrtImpl) : List Artifact := [
  (Spec.RsaPss.signApi Spec.Mgf1.sha256 Spec.Mgf1.sha256).artifact X86.target {
    suffix := Emit.qualifiedName "" [("sha256", v.stream.suffix), ("crt", c.suffix)]
    code := Proof.RsaPss.X86.Sg.signCode (Proof.RsaPss.X86.sha256 v) c
    stack := Proof.RsaPss.X86.Sg.stackBytes
    verified := Proof.RsaPss.X86.Sg.sign_verified (Proof.RsaPss.X86.sha256 v) Proof.RsaPss.X86.Sg.sign_sat_sha256 c
    spSafe := Proof.RsaPss.X86.Sg.code_sp (Proof.RsaPss.X86.sha256 v) c
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.Sha256.RsaPrivateCrt.X86.RsaPssSha256
