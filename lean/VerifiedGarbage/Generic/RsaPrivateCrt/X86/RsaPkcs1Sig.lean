module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignStackSafety
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignVerified
public import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
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
public import VerifiedGarbage.Proof.Mont.X86.ExponentInitMath
public import VerifiedGarbage.Proof.Mont.X86.ExponentMask
public import VerifiedGarbage.Proof.Mont.X86.ExponentShift
public import VerifiedGarbage.Proof.Mont.X86.ExponentTimingBlocks
public import VerifiedGarbage.Proof.Mont.X86.ExponentWord
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
public import VerifiedGarbage.TCB.X86.Print

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
