module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Callees
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCtx
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCCt
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCVerified
public import VerifiedGarbage.Proof.RsaPss.X86_64.Instances

/-!
# RSASSA-PSS signing on x86-64

A generic file of two interfaces (see `TCB/Emit.lean`):
`vg_rsa_pss_<H>_mgf1_<H>_sign`, for the hash function of an `MdHash` variant
`v` with MGF1 over the same hash function, calling `v`'s
`vg_rsa_pss_<H>_mgf1_<H>_encode` (`Generic/MdHash/X86_64/RsaPss.lean`), and
`vg_rsa_private_checked` calling an implementation `c` of
`vg_rsa_private_crt` (`Variants/RsaPrivateCrt/X86_64/`). It is emitted once
for each pair, named by `Emit.qualifiedName` with the hash function's name
and `crt` as tags (e.g. `vg_rsa_pss_sha256_mgf1_sha256_sign_sha256_shani_crt_adx`),
and needs both's CPU features.

Its stack is its frame, a return address and `vg_rsa_private_checked`'s
3256 bytes, more than `encode`'s.
-/

@[expose] public section

namespace VG.Generic.MdHash.RsaPrivateCrt.X86_64.RsaPss

open VG.Proof.RsaPkcs1Enc.X86_64 (privOf)
open VG.Proof.RsaPss.X86_64 (signStack signC_verified signC_spAll encOf)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) (c : Proof.Rsa.X86_64.CrtImpl) : List Artifact := [
  (Spec.RsaPss.signApi v.mgf.G v.mgf.G).artifact X86_64.target {
    suffix := Emit.qualifiedName "" [(v.mgf.G.rust, v.suffix), ("crt", c.suffix)]
    notes := ["This implementation calls `" ++ (encOf v).name ++ "` for EMSA-PSS's encoding, \
      after a zero byte if the modulus' first byte is 1, and signs it with `" ++ (privOf c).name ++
      "`, which checks the signature against `e`. Only the lengths, `salt_len` and the public key \
      decide a branch or an address."]
    code := Impl.RsaPss.X86_64.signC (encOf v).name (encOf v).code (privOf c).name (privOf c).code
    stack := signStack
    verified := signC_verified (hvE := (encOf v).ok) (hctE := (encOf v).ct)
      (hspE := X86_64.SpSafe.of_all (Code.all_of_allInstrs (encOf v).spSafe)) (hdE := (encOf v).depth)
      (hct := (privOf c).ct) (hdC := (privOf c).depth) v.H v.mgf.mem (privOf c).ok
      (X86_64.SpSafe.of_all (privOf c).spSafe)
    spSafe := Code.all_of_allInstrs (signC_spAll (X86_64.SpSafe.of_all (Code.all_of_allInstrs (encOf v).spSafe))
      (X86_64.SpSafe.of_all (privOf c).spSafe))
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.MdHash.RsaPrivateCrt.X86_64.RsaPss
