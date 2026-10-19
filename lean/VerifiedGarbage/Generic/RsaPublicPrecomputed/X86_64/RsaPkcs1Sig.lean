module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.PrecomputedCT
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecPcCT
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Bignum.LazyMath
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
public import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
public import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
public import VerifiedGarbage.Proof.Bignum.X86_64.Copy
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtContract
public import VerifiedGarbage.Proof.Bignum.X86_64.Csub
public import VerifiedGarbage.Proof.Bignum.X86_64.Double
public import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
public import VerifiedGarbage.Proof.Bignum.X86_64.PcMain
public import VerifiedGarbage.Proof.Bignum.X86_64.PdExp
public import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
public import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
public import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
public import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
public import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
public import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
public import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
public import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
public import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
public import VerifiedGarbage.Proof.Bignum.X86_64.Row
public import VerifiedGarbage.Proof.Bignum.X86_64.Setup
public import VerifiedGarbage.Proof.Bignum.X86_64.Store
public import VerifiedGarbage.Proof.Bignum.X86_64.Valid
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Rsa.X86_64.ExpCheck
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivFrame
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncEM
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Recover
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Compare
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCT
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCorrect
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtContract
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PcMain
import VerifiedGarbage.Proof.Bignum.X86_64.PdExp
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Rsa.X86_64.ExpCheck
import VerifiedGarbage.Proof.Rsa.X86_64.PrivFrame
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncEM
import VerifiedGarbage.Proof.RsaPkcs1Sig.Recover
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Compare
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCorrect

/-! # PKCS #1 v1.5 verification and recovery over precomputed RSA public variants -/

@[expose] public section

namespace VG.Generic.RsaPublicPrecomputed.X86_64.RsaPkcs1Sig

open VG.Proof.Rsa.X86_64 (PublicImpl)
open VG.Proof.RsaPkcs1Sig.X86_64

def artifacts (v : PublicImpl) : List Artifact := [
  Spec.RsaPkcs1Sig.verifyPrecomputedApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["This implementation calls `" ++ v.name ++
      "` with the cached modulus values, then compares the recovered encoding with EMSA-PKCS1-v1_5's \
      encoding of `digest`. It combines the padding result with the public operation's status without \
      branching on that status. It uses 2144 bytes of stack, including the call's return address."]
    code := Impl.RsaPkcs1Sig.X86_64.Precomputed.code v.name v.code
    stack := verStack
    verified := PcCT.code_verified v
    spSafe := PcCT.code_spSafe v
    features := v.features },
  Spec.RsaPkcs1Sig.recoverPrecomputedApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["This implementation calls `" ++ v.name ++
      "` with the cached modulus values into its frame, writes EMSA-PKCS1-v1_5's encoding of the last \
      `out_len` bytes of the result beside it and compares the two, then copies those bytes to `out` and \
      masks them to zeros, and the result to 0, unless the public operation succeeded and the two are \
      equal: nothing after the call branches on its result. It uses 2144 bytes of stack, including \
      the call's return address."]
    code := Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.code v.name v.code
    stack := verStack
    verified := RecPcCT.code_verified v
    spSafe := RecPcCT.code_spSafe v
    features := v.features }]

end VG.Generic.RsaPublicPrecomputed.X86_64.RsaPkcs1Sig
