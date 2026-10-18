module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignPcCt
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivPcImpl
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Callees
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSASSA-PSS signing on x86-64

A generic file of two interfaces (see `TCB/Emit.lean`):
`vg_rsa_pss_<H>_mgf1_<H>_sign_precomputed`, for the hash function of an
`MdHash` variant `v` with MGF1 over the same hash function, calling `v`'s
compression function, and `vg_rsa_private_checked_precomputed` calling an
implementation `c` of `vg_rsa_private_crt_precomputed`
(`Variants/RsaPrivateCrt/X86_64/`). It is emitted once for each pair, named
by `Emit.qualifiedName` with the hash function's name and `crt` as tags
(e.g. `vg_rsa_pss_sha256_mgf1_sha256_sign_precomputed_sha256_shani_crt_adx`),
and needs both's CPU features. The Rust code signs with it on x86-64, so
`vg_rsa_pss_<H>_mgf1_<H>_sign` is not emitted here.

Its stack is its frame, a return address and
`vg_rsa_private_checked_precomputed`'s 1208 bytes.
-/

@[expose] public section

namespace VG.Generic.MdHash.RsaPrivateCrt.X86_64.RsaPss

open VG.Proof.RsaPkcs1Enc.X86_64 (privOf)
open VG.Proof.Rsa.X86_64 (privPcOf)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) (c : Proof.Rsa.X86_64.CrtImpl) : List Artifact := [
  (Spec.RsaPss.signPrecomputedApi v.mgf.G v.mgf.G).artifact X86_64.target {
    suffix := Emit.qualifiedName "" [(v.mgf.G.rust, v.suffix), ("crt", c.suffix)]
    notes := ["This implementation builds EMSA-PSS's \
      encoding in its working space: `M'` is hashed over the blocks its length needs, `DB` is \
      masked with MGF1, and the encoding is signed with `" ++ (privPcOf c).name ++ "`, which checks \
      the signature against `e`. Only the lengths, `salt_len`, the public key and the values of `n` in \
      `pre` decide a branch or an address."]
    code := Impl.RsaPss.X86_64.signPc v.H (privPcOf c).name (privPcOf c).code
    stack := Proof.RsaPss.X86_64.SgnPc.signStack
    verified := Proof.RsaPss.X86_64.SgnPc.sign_verified (hct := (privPcOf c).ct)
      (hdC := (privPcOf c).depth) (hH := v.ok) (K := v.K) (lk := v.mgf) (hc := v.pss)
      (privPcOf c).ok (X86_64.SpSafe.of_all (privPcOf c).spSafe)
    spSafe := Code.all_of_allInstrs
      (Proof.RsaPss.X86_64.SgnPc.sign_spAll v.ok v.K (X86_64.SpSafe.of_all (privPcOf c).spSafe))
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.MdHash.RsaPrivateCrt.X86_64.RsaPss
