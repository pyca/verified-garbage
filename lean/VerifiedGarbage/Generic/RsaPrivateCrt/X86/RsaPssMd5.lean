module

public import VerifiedGarbage.Proof.RsaPss.X86.SgVerified
public import VerifiedGarbage.Proof.RsaPss.X86.SgSat
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.X86.Hashes.Md5

/-!
# RSASSA-PSS signing with MD5 on x86, for each implementation of the CRT

A generic file (see `TCB/Emit.lean`): `vg_rsa_pss_md5_mgf1_md5_sign`, calling
`vg_rsa_private_checked` over an implementation `c` of `vg_rsa_private_crt`
(`Variants/RsaPrivateCrt/X86/`), is emitted once for each, named with its
suffix, and needs its CPU features.

It uses 3552 bytes of stack: the push of the registers (16 bytes), its
frame (144 bytes) and the 3392 bytes of `vg_rsa_private_checked`'s, which
are more than the hash function's calls use.
-/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.X86.RsaPssMd5

open VG.Proof.Rsa.X86.PrivChecked (CrtImpl)

def artifacts (c : CrtImpl) : List Artifact := [
  (Spec.RsaPss.signApi Spec.Mgf1.md5 Spec.Mgf1.md5).artifact X86.target {
    suffix := c.suffix
    code := Proof.RsaPss.X86.Sg.signCode Proof.RsaPss.X86.md5 c
    stack := Proof.RsaPss.X86.Sg.stackBytes
    verified := Proof.RsaPss.X86.Sg.sign_verified Proof.RsaPss.X86.md5 Proof.RsaPss.X86.Sg.sign_sat_md5 c
    spSafe := Proof.RsaPss.X86.Sg.code_sp Proof.RsaPss.X86.md5 c
    features := c.features }]

end VG.Generic.RsaPrivateCrt.X86.RsaPssMd5
