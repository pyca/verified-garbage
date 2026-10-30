module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignStackSafety
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignVerified
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
public import VerifiedGarbage.Proof.Bignum.FrameOutside
public import VerifiedGarbage.Proof.Bignum.MemoryFrame
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.X86.ByteOps
public import VerifiedGarbage.Proof.Bignum.X86.CopyByteStep
public import VerifiedGarbage.Proof.Bignum.X86.CopyRegion
public import VerifiedGarbage.Proof.Bignum.X86.ReverseByteStep
public import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
public import VerifiedGarbage.Proof.Cast5.X86.Run
public import VerifiedGarbage.Proof.Dsa.Arithmetic
public import VerifiedGarbage.Proof.Dsa.Digest
public import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Proof.Dsa.Random
public import VerifiedGarbage.Proof.Dsa.RandomEncoding
public import VerifiedGarbage.Proof.Dsa.RandomSign
public import VerifiedGarbage.Proof.Dsa.RandomSignResult
public import VerifiedGarbage.Proof.Dsa.RandomTrace
public import VerifiedGarbage.Proof.Dsa.X86.Bytes
public import VerifiedGarbage.Proof.Dsa.X86.CoreSetup
public import VerifiedGarbage.Proof.Dsa.X86.EntrySave
public import VerifiedGarbage.Proof.Dsa.X86.FailureLoop
public import VerifiedGarbage.Proof.Dsa.X86.FetchByte
public import VerifiedGarbage.Proof.Dsa.X86.Layout
public import VerifiedGarbage.Proof.Dsa.X86.LoadSlot
public import VerifiedGarbage.Proof.Dsa.X86.LocalOperand
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Dsa.X86.RandomAttempt
public import VerifiedGarbage.Proof.Dsa.X86.RandomBody
public import VerifiedGarbage.Proof.Dsa.X86.RandomCallArgs
public import VerifiedGarbage.Proof.Dsa.X86.RandomPrepare
public import VerifiedGarbage.Proof.Dsa.X86.RandomSample
public import VerifiedGarbage.Proof.Dsa.X86.RandomSignCorrect
public import VerifiedGarbage.Proof.Dsa.X86.Reduce
public import VerifiedGarbage.Proof.Dsa.X86.RunBytes
public import VerifiedGarbage.Proof.Dsa.X86.SaveArgument
public import VerifiedGarbage.Proof.Dsa.X86.StackArgument
public import VerifiedGarbage.Proof.Dsa.X86.StageFrame
public import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Dsa.Zero
public import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Mont.X86.ContextLayout
public import VerifiedGarbage.Proof.Mont.X86.ContextMath
public import VerifiedGarbage.Proof.Mont.X86.ContextMul
public import VerifiedGarbage.Proof.Mont.X86.DynamicAdd
public import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
public import VerifiedGarbage.Proof.Mont.X86.DynamicSelect
public import VerifiedGarbage.Proof.Mont.X86.ExponentInitMath
public import VerifiedGarbage.Proof.Mont.X86.ExponentLoop
public import VerifiedGarbage.Proof.Mont.X86.ExponentMask
public import VerifiedGarbage.Proof.Mont.X86.ExponentShift
public import VerifiedGarbage.Proof.Mont.X86.ExponentStep
public import VerifiedGarbage.Proof.Mont.X86.ExponentTimingBlocks
public import VerifiedGarbage.Proof.Mont.X86.ExponentWord
public import VerifiedGarbage.Proof.Mont.X86.Exponentiate
public import VerifiedGarbage.Proof.Mont.X86.Inverse
public import VerifiedGarbage.Proof.Mont.X86.PowerInit
public import VerifiedGarbage.Proof.Mont.X86.PowerLoop
public import VerifiedGarbage.Proof.Mont.X86.PowerTiming
public import VerifiedGarbage.Proof.Mont.X86.PowerTwo
public import VerifiedGarbage.Proof.Mont.X86.RowW
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Rsa.AcceptanceMask32
public import VerifiedGarbage.Proof.Rsa.BytesFrame
public import VerifiedGarbage.Proof.Rsa.Octets
public import VerifiedGarbage.Proof.Rsa.PrivCheckLogic32
public import VerifiedGarbage.Proof.Rsa.Scratch
public import VerifiedGarbage.Proof.Rsa.X86.PrivABI
public import VerifiedGarbage.Proof.Rsa.X86.PrivBody
public import VerifiedGarbage.Proof.Rsa.X86.PrivBodyTiming
public import VerifiedGarbage.Proof.Rsa.X86.PrivCallInput
public import VerifiedGarbage.Proof.Rsa.X86.PrivCallPublic
public import VerifiedGarbage.Proof.Rsa.X86.PrivCallsTiming
public import VerifiedGarbage.Proof.Rsa.X86.PrivCheck
public import VerifiedGarbage.Proof.Rsa.X86.PrivCompare
public import VerifiedGarbage.Proof.Rsa.X86.PrivCompareBuffer
public import VerifiedGarbage.Proof.Rsa.X86.PrivCompareStep
public import VerifiedGarbage.Proof.Rsa.X86.PrivContract
public import VerifiedGarbage.Proof.Rsa.X86.PrivContractInput
public import VerifiedGarbage.Proof.Rsa.X86.PrivCrtCall
public import VerifiedGarbage.Proof.Rsa.X86.PrivEntryReady
public import VerifiedGarbage.Proof.Rsa.X86.PrivFn
public import VerifiedGarbage.Proof.Rsa.X86.PrivFnTiming
public import VerifiedGarbage.Proof.Rsa.X86.PrivLocalArgument
public import VerifiedGarbage.Proof.Rsa.X86.PrivMasks
public import VerifiedGarbage.Proof.Rsa.X86.PrivNoSp
public import VerifiedGarbage.Proof.Rsa.X86.PrivObservations
public import VerifiedGarbage.Proof.Rsa.X86.PrivPrecomputeLength
public import VerifiedGarbage.Proof.Rsa.X86.PrivPublicCall
public import VerifiedGarbage.Proof.Rsa.X86.PrivRegions
public import VerifiedGarbage.Proof.Rsa.X86.PrivRelease
public import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseBuffer
public import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseStep
public import VerifiedGarbage.Proof.Rsa.X86.PrivRestore
public import VerifiedGarbage.Proof.Rsa.X86.PrivRetained
public import VerifiedGarbage.Proof.Rsa.X86.PrivReturn
public import VerifiedGarbage.Proof.Rsa.X86.PrivSaveStatus
public import VerifiedGarbage.Proof.Rsa.X86.PrivSetupTiming
public import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
public import VerifiedGarbage.Proof.Rsa.X86.PrivStackWord
public import VerifiedGarbage.Proof.Rsa.X86.PrivStatusMask
public import VerifiedGarbage.Proof.Rsa.X86.PrivTailContext
public import VerifiedGarbage.Proof.Rsa.X86.PrivTailTiming
public import VerifiedGarbage.Proof.Rsa.X86.PrivVerified
public import VerifiedGarbage.Proof.Rsa.X86.PrivZeroTest
public import VerifiedGarbage.Proof.Rsa.ZeroTest32
public import VerifiedGarbage.Proof.RsaPkcs1Sig.ByteMath
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Encode
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeChecks
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeCopyStep
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeHash
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeHead
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodePadding
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeWrite
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignABI
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignBlocksTiming
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignBody
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignBodyTiming
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignCallPublic
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignContract
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignContractInput
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignEncArgs
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignEntryReady
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignEraseTiming
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignFn
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignFnTiming
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignLocalArgument
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignNoSp
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignObservations
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignPrivateRegions
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignRegions
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignRestore
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignReturn
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignStackWord
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignWipe
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignWipeArgs
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignZero
public import VerifiedGarbage.Proof.RsaPss.Params
public import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
public import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
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
import VerifiedGarbage.Proof.Dsa.X86.LoadSlot
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
import VerifiedGarbage.Proof.Mont.X86.DynamicSelect
import VerifiedGarbage.Proof.Mont.X86.ExponentInitMath
import VerifiedGarbage.Proof.Mont.X86.ExponentLoop
import VerifiedGarbage.Proof.Mont.X86.ExponentMask
import VerifiedGarbage.Proof.Mont.X86.ExponentShift
import VerifiedGarbage.Proof.Mont.X86.ExponentStep
import VerifiedGarbage.Proof.Mont.X86.ExponentTimingBlocks
import VerifiedGarbage.Proof.Mont.X86.ExponentWord
import VerifiedGarbage.Proof.Mont.X86.Exponentiate
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
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignBody
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignBodyTiming
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignCallPublic
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignContract
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignContractInput
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignEncArgs
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignEntryReady
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignEraseTiming
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignFn
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

/-! # PKCS #1 signing follows every i686 private CRT implementation -/

@[expose] public section
namespace VG.Generic.RsaPrivateCrt.X86.RsaPkcs1Sig
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl privCode)
open VG.Proof.RsaPkcs1Sig.X86.Sgn

def artifacts (v : CrtImpl) : List Artifact := [
  Spec.RsaPkcs1Sig.signApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.RsaPkcs1Sig.X86.Sign.code (privName v) (privCode v)
    stack := sigStack
    verified := sign_verified v
    spSafe := code_sp v
    features := v.features }]

end VG.Generic.RsaPrivateCrt.X86.RsaPkcs1Sig
