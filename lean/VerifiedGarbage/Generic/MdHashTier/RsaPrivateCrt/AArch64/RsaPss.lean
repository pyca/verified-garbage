module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Tier
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPss.AArch64.Instances
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
import VerifiedGarbage.Proof.Sha512.Word64
import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSASSA-PSS signing on AArch64

A generic file of two interfaces (see `TCB/Emit.lean`): `vg_rsa_pss_sign`
calls the hash functions `hash` and `mgf1_hash` name, of the tier `t`
(`Variants/MdHashTier/AArch64/`), through a dispatch on each number, and an
implementation `c` of `vg_rsa_private_crt`. It is emitted for each pair,
named by `Emit.qualifiedName` (`hash` for the tier, then `crt`), and needs
both's CPU features. Its stack is its frame and `vg_rsa_private_checked`'s
3248 bytes.
-/

@[expose] public section

namespace VG.Generic.MdHashTier.RsaPrivateCrt.AArch64.RsaPss

open VG.Proof.RsaPkcs1Sig.AArch64 (privOf)
open VG.Proof.RsaPss.AArch64 (tierHs sign_verified)
open VG.Proof.RsaPss.AArch64.Inst (features)
open VG.Proof.RsaPss.AArch64.Sgn (stk)

def artifacts (t : Proof.Pbkdf2.Md.AArch64.Tier) (c : Proof.Rsa.AArch64.CrtImpl) : List Artifact := [
  Spec.RsaPss.signAnyApi.artifact AArch64.target {
    suffix := Emit.qualifiedName "" [("hash", t.suffix), ("crt", c.suffix)]
    notes := ["This implementation builds EMSA-PSS's \
      encoding in its working space: `M'` is hashed over the blocks its length needs, `DB` is \
      masked with MGF1, and the encoding is signed with `" ++ (privOf c).name ++ "`, which checks \
      the signature against `e`. The hash functions `hash` and `mgf1_hash` name are called \
      through a dispatch on each number, which is public. Only the lengths, `salt_len`, the hash \
      functions and the public key decide a branch or an address."]
    code := Impl.RsaPss.AArch64.sign (tierHs t) (privOf c).name (privOf c).code
    stack := stk (privOf c).stack
    verified := sign_verified t c
    features := features t c.features }]

end VG.Generic.MdHashTier.RsaPrivateCrt.AArch64.RsaPss
