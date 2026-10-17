module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Tier
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPss.X86_64.AnySignVerified
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Callees
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSASSA-PSS signing on x86-64, with the hash functions as arguments

A generic file of two interfaces (see `TCB/Emit.lean`): `vg_rsa_pss_sign`,
for the hash functions of a tier `t` (`Variants/MdHashTier/X86_64/`), the
digest's and MGF1's chosen by `hash` and `mgf1_hash`, and
`vg_rsa_private_checked` calling an implementation `c` of
`vg_rsa_private_crt` (`Variants/RsaPrivateCrt/X86_64/`). It is emitted once
for each pair, named by `Emit.qualifiedName` with `hash` and `crt` as tags
(e.g. `vg_rsa_pss_sign_hash_shani_crt_adx`), and needs both's CPU features.

Its stack is its frame, a return address and `vg_rsa_private_checked`'s
3256 bytes.
-/

@[expose] public section

namespace VG.Generic.MdHashTier.RsaPrivateCrt.X86_64.RsaPss

open VG.Proof.RsaPkcs1Enc.X86_64 (privOf)
open VG.Proof.RsaPss.X86_64 (signStack)
open VG.Proof.RsaPss.X86_64.Any (tierHashes tier_ok signAny_verified signAny_spAll)

def artifacts (t : Proof.Pbkdf2.Md.X86_64.Tier) (c : Proof.Rsa.X86_64.CrtImpl) : List Artifact := [
  Spec.RsaPss.signAnyApi.artifact X86_64.target {
    suffix := Emit.qualifiedName "" [("hash", t.suffix), ("crt", c.suffix)]
    notes := ["This implementation builds EMSA-PSS's \
      encoding in its working space: `M'` is hashed over the blocks its length needs, `DB` is \
      masked with MGF1, and the encoding is signed with `" ++ (privOf c).name ++ "`, which checks \
      the signature against `e`. The hash functions are chosen by comparing `hash` and `mgf1_hash` \
      with each number in turn. Only the lengths, `salt_len`, `hash`, `mgf1_hash` and the public \
      key decide a branch or an address."]
    code := Impl.RsaPss.X86_64.AnyHash.sign (tierHashes t) (privOf c).name (privOf c).code
    stack := signStack
    verified := signAny_verified t (hct := (privOf c).ct) (hdC := (privOf c).depth)
      (privOf c).ok (X86_64.SpSafe.of_all (privOf c).spSafe)
    spSafe := Code.all_of_allInstrs (signAny_spAll (tierHashes t) (tier_ok t)
      (X86_64.SpSafe.of_all (privOf c).spSafe))
    features := t.features ++ c.features.filter (!t.features.contains ·) }]

end VG.Generic.MdHashTier.RsaPrivateCrt.X86_64.RsaPss
