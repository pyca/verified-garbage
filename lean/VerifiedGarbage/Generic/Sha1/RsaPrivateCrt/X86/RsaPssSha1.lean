module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPss.X86.SgVerified
public import VerifiedGarbage.Proof.RsaPss.X86.SgSat
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.X86.Hashes.Sha1

/-!
# RSASSA-PSS signing with SHA-1 on x86, for each SHA-1 backend and implementation of the CRT

A generic file of two interfaces (see `TCB/Emit.lean`):
`vg_rsa_pss_sha1_mgf1_sha1_sign` hashes with the streaming and compression
functions of a backend `v` (`Variants/Sha1/X86/`), and calls
`vg_rsa_private_checked` over an implementation `c` of
`vg_rsa_private_crt` (`Variants/RsaPrivateCrt/X86/`). It is emitted once for
each pair, named by `Emit.qualifiedName` with the tags `sha1` and
`crt`, and needs both's CPU features.

It uses 3552 bytes of stack: the push of the registers (16 bytes), its
frame (144 bytes) and the 3392 bytes of `vg_rsa_private_checked`'s, which
are more than the hash function's calls use.
-/

@[expose] public section

namespace VG.Generic.Sha1.RsaPrivateCrt.X86.RsaPssSha1

open VG.Proof.Rsa.X86.PrivChecked (CrtImpl)

def artifacts (v : Proof.Sha1.X86.Variants.Backend) (c : CrtImpl) : List Artifact := [
  (Spec.RsaPss.signApi Spec.Mgf1.sha1 Spec.Mgf1.sha1).artifact X86.target {
    suffix := Emit.qualifiedName "" [("sha1", v.stream.suffix), ("crt", c.suffix)]
    notes := ["This implementation builds EMSA-PSS's encoding in its working space: `M'` is hashed \
      over the blocks its length needs, `DB` is masked with MGF1, and the encoding is signed with `" ++
      Proof.RsaPss.X86.Sg.privName c ++ "`, which checks the signature against `e`. Only the lengths, \
      `salt_len` and the public key decide a branch or an address."]
    code := Proof.RsaPss.X86.Sg.signCode (Proof.RsaPss.X86.sha1 v) c
    stack := Proof.RsaPss.X86.Sg.stackBytes
    verified := Proof.RsaPss.X86.Sg.sign_verified (Proof.RsaPss.X86.sha1 v) Proof.RsaPss.X86.Sg.sign_sat_sha1 c
    spSafe := Proof.RsaPss.X86.Sg.code_sp (Proof.RsaPss.X86.sha1 v) c
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.Sha1.RsaPrivateCrt.X86.RsaPssSha1
