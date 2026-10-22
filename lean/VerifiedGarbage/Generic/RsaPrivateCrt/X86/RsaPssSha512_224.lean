module

public import VerifiedGarbage.Proof.RsaPss.X86.SgVerified
public import VerifiedGarbage.Proof.RsaPss.X86.SgSat
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.X86.Hashes.Sha512

/-!
# RSASSA-PSS signing with SHA-512/224 on x86, for each implementation of the CRT

A generic file (see `TCB/Emit.lean`): `vg_rsa_pss_sha512_224_mgf1_sha512_224_sign`, calling
`vg_rsa_private_checked` over an implementation `c` of `vg_rsa_private_crt`
(`Variants/RsaPrivateCrt/X86/`), is emitted once for each, named with its
suffix, and needs its CPU features.

It uses 3552 bytes of stack: the push of the registers (16 bytes), its
frame (144 bytes) and the 3392 bytes of `vg_rsa_private_checked`'s, which
are more than the hash function's calls use.
-/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.X86.RsaPssSha512_224

open VG.Proof.Rsa.X86.PrivChecked (CrtImpl)

def artifacts (c : CrtImpl) : List Artifact := [
  (Spec.RsaPss.signApi Spec.Mgf1.sha512_224 Spec.Mgf1.sha512_224).artifact X86.target {
    suffix := c.suffix
    notes := ["This implementation builds EMSA-PSS's encoding in its working space: `M'` is hashed \
      over the blocks its length needs, `DB` is masked with MGF1, and the encoding is signed with `" ++
      Proof.RsaPss.X86.Sg.privName c ++ "`, which checks the signature against `e`. Only the lengths, \
      `salt_len` and the public key decide a branch or an address."]
    code := Proof.RsaPss.X86.Sg.signCode Proof.RsaPss.X86.sha512_224 c
    stack := Proof.RsaPss.X86.Sg.stackBytes
    verified := Proof.RsaPss.X86.Sg.sign_verified Proof.RsaPss.X86.sha512_224 Proof.RsaPss.X86.Sg.sign_sat_sha512_224 c
    spSafe := Proof.RsaPss.X86.Sg.code_sp Proof.RsaPss.X86.sha512_224 c
    features := c.features }]

end VG.Generic.RsaPrivateCrt.X86.RsaPssSha512_224
