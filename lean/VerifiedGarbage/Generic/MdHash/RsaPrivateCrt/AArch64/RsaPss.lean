module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPss.AArch64.Instances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
import VerifiedGarbage.Proof.Sha512.Word64
import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
public import VerifiedGarbage.Proof.Framework.Cold
public import VerifiedGarbage.Proof.Framework.EntryBranch
public import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Hmac.AnyKey
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.AnyKeyEntry
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.Proof.RsaPss.AArch64.CtHash
public import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT
public import VerifiedGarbage.Proof.RsaPss.AArch64.CtPadEq
public import VerifiedGarbage.Proof.RsaPss.AArch64.EmView
public import VerifiedGarbage.Proof.RsaPss.AArch64.FixedSaltCT
public import VerifiedGarbage.Proof.RsaPss.AArch64.MgfCT
public import VerifiedGarbage.Proof.RsaPss.AArch64.RelSplit
public import VerifiedGarbage.Proof.RsaPss.AArch64.Select
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignBody
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignCT
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignCorrect
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignEncOk
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignTop
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignVerified
public import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyBody
public import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyCT
public import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyTop
public import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyVerified
public import VerifiedGarbage.Proof.RsaPss.Encoding
public import VerifiedGarbage.Proof.RsaPss.MgfBytes
public import VerifiedGarbage.Proof.RsaPss.Params
public import VerifiedGarbage.Proof.RsaPss.SignCases
public import VerifiedGarbage.Proof.Sha256.AArch64.Compress
public import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Common
public import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Digest
public import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Init
public import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Digest
public import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Init
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
import VerifiedGarbage.Proof.Framework.Cold
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Hmac.AnyKey
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.AnyKeyEntry
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHash
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT
import VerifiedGarbage.Proof.RsaPss.AArch64.CtPadEq
import VerifiedGarbage.Proof.RsaPss.AArch64.EmView
import VerifiedGarbage.Proof.RsaPss.AArch64.FixedSaltCT
import VerifiedGarbage.Proof.RsaPss.AArch64.MgfCT
import VerifiedGarbage.Proof.RsaPss.AArch64.RelSplit
import VerifiedGarbage.Proof.RsaPss.AArch64.Select
import VerifiedGarbage.Proof.RsaPss.AArch64.SignBody
import VerifiedGarbage.Proof.RsaPss.AArch64.SignCT
import VerifiedGarbage.Proof.RsaPss.AArch64.SignCorrect
import VerifiedGarbage.Proof.RsaPss.AArch64.SignEncOk
import VerifiedGarbage.Proof.RsaPss.AArch64.SignTop
import VerifiedGarbage.Proof.RsaPss.AArch64.SignVerified
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyBody
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyCT
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyTop
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyVerified
import VerifiedGarbage.Proof.RsaPss.Encoding
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaPss.SignCases
import VerifiedGarbage.Proof.Sha256.AArch64.Compress
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Common
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Digest
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Init
import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Digest
import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Init

/-!
# RSASSA-PSS signing on AArch64

Generic over two interfaces: the hash function of an `MdHash` variant `v`
(with MGF1 over the same hash function) and an implementation `c` of
`vg_rsa_private_crt`. Its stack is its frame and `vg_rsa_private_checked`'s
3248 bytes.
-/

@[expose] public section

namespace VG.Generic.MdHash.RsaPrivateCrt.AArch64.RsaPss

open VG.Proof.RsaPkcs1Sig.AArch64 (privOf)
open VG.Proof.RsaPss.AArch64.Sgn (stk)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (c : Proof.Rsa.AArch64.CrtImpl) : List Artifact := [
  (Spec.RsaPss.signApi v.mgf.G v.mgf.G).artifact AArch64.target {
    suffix := Emit.qualifiedName "" [(v.mgf.G.rust, v.suffix), ("crt", c.suffix)]
    notes := ["This implementation builds EMSA-PSS's \
      encoding in its working space: `M'` is hashed over the blocks its length needs, `DB` is \
      masked with MGF1, and the encoding is signed with `" ++ (privOf c).name ++ "`, which checks \
      the signature against `e`. Only the lengths, `salt_len` and the public key decide a branch \
      or an address."]
    code := Impl.RsaPss.AArch64.sign v.H (privOf c).name (privOf c).code
    stack := stk (privOf c).stack
    verified := Proof.RsaPss.AArch64.sign_verified v c
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.MdHash.RsaPrivateCrt.AArch64.RsaPss
