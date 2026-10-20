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
# RSASSA-PSS verification using cached public-key values, on AArch64

Every hash compression variant combines with every precomputed RSA public
operation variant. The digest, signature and recovered encoding stay secret.

Its stack is its frame and 16 bytes below it, for the calls of the hash
function's and the public operation's functions (which have no frames).
-/

@[expose] public section

namespace VG.Generic.MdHash.RsaPublicPrecomputed.AArch64.RsaPss

open VG.Proof.RsaPkcs1Sig.AArch64 (pdOf)
open VG.Proof.RsaPss.AArch64.Sgn (stk)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (c : Proof.Rsa.AArch64.PublicImpl) : List Artifact := [
  (Spec.RsaPss.verifyPrecomputedApi v.mgf.G v.mgf.G).artifact AArch64.target {
    suffix := Emit.qualifiedName "" [(v.mgf.G.rust, v.suffix), ("rsa", c.suffix)]
    notes := ["This implementation calls `" ++ c.name ++ "` with the cached public-key values, \
        then checks EMSA-PSS in its working space without branching on the encoding: `maskedDB` \
        is unmasked with MGF1 and its delimiter and salt length checked. A specified salt length \
        copies that many trailing bytes into `M'` and hashes only the blocks needed; an unknown \
        salt length retains the oblivious shift and maximum block count. Only public lengths, \
        salt-length mode and key data decide a branch or an address."]
    code := Impl.RsaPss.AArch64.verifyPrecomputed v.H (pdOf c).name (pdOf c).code
    stack := stk 16
    verified := Proof.RsaPss.AArch64.verify_verified v c
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.MdHash.RsaPublicPrecomputed.AArch64.RsaPss
