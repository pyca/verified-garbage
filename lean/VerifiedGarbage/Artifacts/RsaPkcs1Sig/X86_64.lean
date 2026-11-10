module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignCT
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Bignum.LazyMath
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
public import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
public import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
public import VerifiedGarbage.Proof.Bignum.X86_64.Copy
public import VerifiedGarbage.Proof.Bignum.X86_64.Csub
public import VerifiedGarbage.Proof.Bignum.X86_64.Double
public import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
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
public import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Rsa.Octets
public import VerifiedGarbage.Proof.Rsa.X86_64.ExpCheck
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCT
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCheck
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCorrect
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivTail
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Recover
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Compare
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCT
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignCorrect
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86_64
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.PrecomputedCT
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecPcCT
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtContract
public import VerifiedGarbage.Proof.Bignum.X86_64.PcMain
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivFrame
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncEM
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCT
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCorrect
public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.X86_64

/-! # RSASSA-PKCS1-v1_5 (RFC 8017) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Sig.X86_64

open VG.Proof.Rsa.X86_64 (PublicImpl)

open VG.Proof.Rsa.X86_64 (CrtImpl)
open VG.Proof.RsaPkcs1Sig.X86_64

def artifacts : List Artifact :=
  (VG.Proof.Variants.RsaPrivateCrt.X86_64.variants.flatMap fun (v : CrtImpl) => [
    Spec.RsaPkcs1Sig.signApi.artifact X86_64.target (Sgn.reg v)]) ++
  (VG.Proof.Variants.RsaPublicPrecomputed.X86_64.variants.flatMap fun (v : PublicImpl) => [
    Spec.RsaPkcs1Sig.verifyPrecomputedApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.RsaPkcs1Sig.X86_64.Precomputed.code v.name v.code
      stack := verStack
      verified := PcCT.code_verified v
      spSafe := PcCT.code_spSafe v },
    Spec.RsaPkcs1Sig.recoverPrecomputedApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.code v.name v.code
      stack := verStack
      verified := RecPcCT.code_verified v
      spSafe := RecPcCT.code_spSafe v }])

end VG.Artifacts.RsaPkcs1Sig.X86_64
