module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Scrub
import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Fn
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverStackSafety
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverVerified
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyStackSafety
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyVerified
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignP.Verified
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.Bignum.FrameOutside
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86.ByteOps
import VerifiedGarbage.Proof.Bignum.X86.CopyByteStep
import VerifiedGarbage.Proof.Bignum.X86.CopyRegion
import VerifiedGarbage.Proof.Bignum.X86.ReverseByteStep
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Cast5.X86.Run
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Random
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Dsa.RandomSign
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Dsa.RandomTrace
import VerifiedGarbage.Proof.Dsa.X86.Bytes
import VerifiedGarbage.Proof.Dsa.X86.CoreSetup
import VerifiedGarbage.Proof.Dsa.X86.EntrySave
import VerifiedGarbage.Proof.Dsa.X86.FailureLoop
import VerifiedGarbage.Proof.Dsa.X86.FetchByte
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.LocalOperand
import VerifiedGarbage.Proof.Dsa.X86.Moduli
import VerifiedGarbage.Proof.Dsa.X86.RandomAttempt
import VerifiedGarbage.Proof.Dsa.X86.RandomBody
import VerifiedGarbage.Proof.Dsa.X86.RandomCallArgs
import VerifiedGarbage.Proof.Dsa.X86.RandomPrepare
import VerifiedGarbage.Proof.Dsa.X86.RandomSample
import VerifiedGarbage.Proof.Dsa.X86.RandomSignCorrect
import VerifiedGarbage.Proof.Dsa.X86.Reduce
import VerifiedGarbage.Proof.Dsa.X86.RunBytes
import VerifiedGarbage.Proof.Dsa.X86.SaveArgument
import VerifiedGarbage.Proof.Dsa.X86.StackArgument
import VerifiedGarbage.Proof.Dsa.X86.StageFrame
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.DynamicAdd
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Mont.X86.ExponentInitMath
import VerifiedGarbage.Proof.Mont.X86.ExponentMask
import VerifiedGarbage.Proof.Mont.X86.ExponentShift
import VerifiedGarbage.Proof.Mont.X86.ExponentTimingBlocks
import VerifiedGarbage.Proof.Mont.X86.ExponentWord
import VerifiedGarbage.Proof.Mont.X86.Inverse
import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Mont.X86.PowerLoop
import VerifiedGarbage.Proof.Mont.X86.PowerTiming
import VerifiedGarbage.Proof.Mont.X86.PowerTwo
import VerifiedGarbage.Proof.Mont.X86.RowW
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Rsa.AcceptanceMask32
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Rsa.PrivCheckLogic32
import VerifiedGarbage.Proof.Rsa.Scratch
import VerifiedGarbage.Proof.Rsa.X86.PrivABI
import VerifiedGarbage.Proof.Rsa.X86.PrivBody
import VerifiedGarbage.Proof.Rsa.X86.PrivBodyTiming
import VerifiedGarbage.Proof.Rsa.X86.PrivCallInput
import VerifiedGarbage.Proof.Rsa.X86.PrivCallPublic
import VerifiedGarbage.Proof.Rsa.X86.PrivCallsTiming
import VerifiedGarbage.Proof.Rsa.X86.PrivCheck
import VerifiedGarbage.Proof.Rsa.X86.PrivCompare
import VerifiedGarbage.Proof.Rsa.X86.PrivCompareBuffer
import VerifiedGarbage.Proof.Rsa.X86.PrivCompareStep
import VerifiedGarbage.Proof.Rsa.X86.PrivContract
import VerifiedGarbage.Proof.Rsa.X86.PrivContractInput
import VerifiedGarbage.Proof.Rsa.X86.PrivCrtCall
import VerifiedGarbage.Proof.Rsa.X86.PrivEntryReady
import VerifiedGarbage.Proof.Rsa.X86.PrivFn
import VerifiedGarbage.Proof.Rsa.X86.PrivFnTiming
import VerifiedGarbage.Proof.Rsa.X86.PrivLocalArgument
import VerifiedGarbage.Proof.Rsa.X86.PrivMasks
import VerifiedGarbage.Proof.Rsa.X86.PrivNoSp
import VerifiedGarbage.Proof.Rsa.X86.PrivObservations
import VerifiedGarbage.Proof.Rsa.X86.PrivPrecomputeLength
import VerifiedGarbage.Proof.Rsa.X86.PrivPublicCall
import VerifiedGarbage.Proof.Rsa.X86.PrivRegions
import VerifiedGarbage.Proof.Rsa.X86.PrivRelease
import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseBuffer
import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseStep
import VerifiedGarbage.Proof.Rsa.X86.PrivRestore
import VerifiedGarbage.Proof.Rsa.X86.PrivRetained
import VerifiedGarbage.Proof.Rsa.X86.PrivReturn
import VerifiedGarbage.Proof.Rsa.X86.PrivSaveStatus
import VerifiedGarbage.Proof.Rsa.X86.PrivSetupTiming
import VerifiedGarbage.Proof.Rsa.X86.PrivStackWord
import VerifiedGarbage.Proof.Rsa.X86.PrivStatusMask
import VerifiedGarbage.Proof.Rsa.X86.PrivTailContext
import VerifiedGarbage.Proof.Rsa.X86.PrivTailTiming
import VerifiedGarbage.Proof.Rsa.X86.PrivVerified
import VerifiedGarbage.Proof.Rsa.X86.PrivZeroTest
import VerifiedGarbage.Proof.Rsa.ZeroTest32
import VerifiedGarbage.Proof.RsaPkcs1Sig.ByteMath
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeChecks
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeCopyStep
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeHash
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeHead
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodePadding
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeWrite
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignABI
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignBlocksTiming
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignBodyTiming
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignCallPublic
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignContractInput
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignEncArgs
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignEntryReady
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignEraseTiming
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignFnTiming
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignLocalArgument
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignNoSp
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignObservations
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignPrivateRegions
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignRegions
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignRestore
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignReturn
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignStackWord
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignWipe
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignWipeArgs
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignZero
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSASSA-PKCS1-v1_5 (RFC 8017) on x86 -/

namespace VG.Artifacts.RsaPkcs1Sig.X86
open VG.Proof.RsaPkcs1Sig.X86.Ver (baseline)

def direct : List (Artifact X86.target) := [
  Spec.RsaPkcs1Sig.verifyPrecomputedApi.artifact VG.X86.target {
    code := Impl.RsaPkcs1Sig.X86.Fn.verifyPrecomputed baseline.name baseline.code
    verified := Proof.RsaPkcs1Sig.X86.Scrub.verifyPrecomputed_scrubbed },
  Spec.RsaPkcs1Sig.recoverPrecomputedApi.artifact VG.X86.target {
    code := Impl.RsaPkcs1Sig.X86.Fn.recoverPrecomputed baseline.name baseline.code
    verified := Proof.RsaPkcs1Sig.X86.Scrub.recoverPrecomputed_scrubbed }]

end VG.Artifacts.RsaPkcs1Sig.X86

namespace VG.Artifacts.RsaPkcs1Sig.X86

open VG.Proof.Rsa.X86.PrivChecked (CrtImpl privCodeP crtPBaseline)
open VG.Proof.RsaPkcs1Sig.X86.Sgn

public def artifacts : List (Artifact X86.target) :=
  direct ++
  (VG.Proof.Variants.RsaPrivateCrt.X86.variants.flatMap fun (v : CrtImpl) => [
    Spec.RsaPkcs1Sig.signPrecomputedApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.RsaPkcs1Sig.X86.Fn.signPrecomputed (privNameP v) (privCodeP v crtPBaseline)
      verified := Proof.RsaPkcs1Sig.X86.Scrub.signPrecomputed_scrubbed v
      spSafe := Proof.RsaPkcs1Sig.X86.Scrub.signPrecomputed_spSafe v }])

spec_apis artifacts

end VG.Artifacts.RsaPkcs1Sig.X86
