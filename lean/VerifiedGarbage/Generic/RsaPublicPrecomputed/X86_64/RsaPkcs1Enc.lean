module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.PcCT
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
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCorrect
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncEM
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
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCorrect
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncEM

/-! # PKCS #1 v1.5 encryption over precomputed RSA public variants -/

@[expose] public section

namespace VG.Generic.RsaPublicPrecomputed.X86_64.RsaPkcs1Enc

open VG.Proof.Rsa.X86_64 (PublicImpl)
open VG.Proof.RsaPkcs1Enc.X86_64

def artifacts (v : PublicImpl) : List Artifact := [
  Spec.RsaPkcs1Enc.encryptPrecomputedApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["This implementation builds \
      `EM = 0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M` in its frame, finding whether `PS` has a zero byte without a \
      branch, and calls `" ++ v.name ++ "` on it with the cached modulus values. It then sets `out` to \
      zeros and the result to 0 under a mask if `PS` had a zero byte, without branching on the public \
      operation's result, and overwrites the frame's `EM` with zeros either way."]
    code := Impl.RsaPkcs1Enc.X86_64.Precomputed.code v.name v.code
    stack := encStack
    verified := PcCT.code_verified v
    spSafe := PcCT.code_spSafe v
    features := v.features }]

end VG.Generic.RsaPublicPrecomputed.X86_64.RsaPkcs1Enc
