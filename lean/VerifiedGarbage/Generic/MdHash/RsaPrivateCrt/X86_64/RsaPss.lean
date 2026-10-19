module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCt
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Callees
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCtx
public import VerifiedGarbage.Proof.Sha256.X86_64.Lit
import VerifiedGarbage.Proof.RsaPss.X86_64.SignVerified

/-!
# RSASSA-PSS signing on x86-64

A generic file of two interfaces (see `TCB/Emit.lean`):
`vg_rsa_pss_<H>_mgf1_<H>_sign`, for the hash function of an `MdHash` variant
`v` with MGF1 over the same hash function, calling `v`'s compression
function, and `vg_rsa_private_checked` calling an implementation `c` of
`vg_rsa_private_crt` (`Variants/RsaPrivateCrt/X86_64/`). It is emitted once
for each pair, named by `Emit.qualifiedName` with the hash function's name
and `crt` as tags (e.g. `vg_rsa_pss_sha256_mgf1_sha256_sign_sha256_shani_crt_adx`),
and needs both's CPU features.

Its stack is its frame, a return address and `vg_rsa_private_checked`'s
3256 bytes.
-/

@[expose] public section

namespace VG.Generic.MdHash.RsaPrivateCrt.X86_64.RsaPss

open VG.Proof.RsaPkcs1Enc.X86_64 (privOf)
open VG.Proof.RsaPss.X86_64 (signStack sign_verified sign_spAll)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) (c : Proof.Rsa.X86_64.CrtImpl) : List Artifact := [
  (Spec.RsaPss.signApi v.mgf.G v.mgf.G).artifact X86_64.target {
    suffix := Emit.qualifiedName "" [(v.mgf.G.rust, v.suffix), ("crt", c.suffix)]
    notes := ["This implementation builds EMSA-PSS's \
      encoding in its working space: `M'` is hashed over the blocks its length needs, `DB` is \
      masked with MGF1, and the encoding is signed with `" ++ (privOf c).name ++ "`, which checks \
      the signature against `e`. Only the lengths, `salt_len` and the public key decide a branch \
      or an address."]
    code := Impl.RsaPss.X86_64.sign v.H (privOf c).name (privOf c).code
    stack := signStack
    verified := sign_verified (hct := (privOf c).ct)
      (hdC := (privOf c).depth) (hH := v.ok) (K := v.K) (lk := v.mgf) (hc := v.pss)
      (privOf c).ok (X86_64.SpSafe.of_all (privOf c).spSafe)
    spSafe := Code.all_of_allInstrs (sign_spAll v.ok v.K (X86_64.SpSafe.of_all (privOf c).spSafe))
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.MdHash.RsaPrivateCrt.X86_64.RsaPss
