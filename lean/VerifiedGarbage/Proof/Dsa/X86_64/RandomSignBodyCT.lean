module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignLoopCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignInitCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFinishAgreement
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignLoopCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignInitCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFinishAgreement
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSingleCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignBody
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.R2wCT
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.Random
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Dsa.RandomSign
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Dsa.RandomSignTrace
import VerifiedGarbage.Proof.Dsa.RandomTrace
import VerifiedGarbage.Proof.Dsa.RandomTraceResult
import VerifiedGarbage.Proof.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.X86_64.AcceptedSpec
import VerifiedGarbage.Proof.Dsa.X86_64.Add
import VerifiedGarbage.Proof.Dsa.X86_64.AddCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
import VerifiedGarbage.Proof.Dsa.X86_64.BufferFrame
import VerifiedGarbage.Proof.Dsa.X86_64.CTBlocks
import VerifiedGarbage.Proof.Dsa.X86_64.Call2
import VerifiedGarbage.Proof.Dsa.X86_64.CallAddCT
import VerifiedGarbage.Proof.Dsa.X86_64.CallOperands
import VerifiedGarbage.Proof.Dsa.X86_64.Child
import VerifiedGarbage.Proof.Dsa.X86_64.CopyMasked
import VerifiedGarbage.Proof.Dsa.X86_64.DeriveCopy
import VerifiedGarbage.Proof.Dsa.X86_64.DeriveFailure
import VerifiedGarbage.Proof.Dsa.X86_64.DeriveMainCT
import VerifiedGarbage.Proof.Dsa.X86_64.DeriveVerified
import VerifiedGarbage.Proof.Dsa.X86_64.DomainShapeCT
import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
import VerifiedGarbage.Proof.Dsa.X86_64.EnterLeave
import VerifiedGarbage.Proof.Dsa.X86_64.EntryFieldsFrame
import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
import VerifiedGarbage.Proof.Dsa.X86_64.Exponent
import VerifiedGarbage.Proof.Dsa.X86_64.Failure
import VerifiedGarbage.Proof.Dsa.X86_64.KeyPointers
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Dsa.X86_64.Masks
import VerifiedGarbage.Proof.Dsa.X86_64.Minus
import VerifiedGarbage.Proof.Dsa.X86_64.MinusStep
import VerifiedGarbage.Proof.Dsa.X86_64.Multiply
import VerifiedGarbage.Proof.Dsa.X86_64.OneScanCT
import VerifiedGarbage.Proof.Dsa.X86_64.OrWords
import VerifiedGarbage.Proof.Dsa.X86_64.ParametersVerified
import VerifiedGarbage.Proof.Dsa.X86_64.Parent
import VerifiedGarbage.Proof.Dsa.X86_64.Parity
import VerifiedGarbage.Proof.Dsa.X86_64.Power
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Dsa.X86_64.PublicKeyCT
import VerifiedGarbage.Proof.Dsa.X86_64.PublicPrefix
import VerifiedGarbage.Proof.Dsa.X86_64.PublicSlices
import VerifiedGarbage.Proof.Dsa.X86_64.RandomBorrow
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopy
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyCandidate
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyInit
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyWhole
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDraw
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawCheckCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawCopy
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawFinishCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawRange
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFunctional
import VerifiedGarbage.Proof.Dsa.X86_64.RandomInRange
import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
import VerifiedGarbage.Proof.Dsa.X86_64.RandomNonceEncoding
import VerifiedGarbage.Proof.Dsa.X86_64.RandomPrepare
import VerifiedGarbage.Proof.Dsa.X86_64.RandomPrepareFinish
import VerifiedGarbage.Proof.Dsa.X86_64.RandomPrepareState
import VerifiedGarbage.Proof.Dsa.X86_64.RandomRange
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSample
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleAgreement
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleLoop
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleLoopCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomScan
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignArgsSaved
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignAttempt
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignAttemptCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallGeometry
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallMemory
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallObserve
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallPre
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallRetry
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallValue
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCode
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFinish
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignInit
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignInvalid
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignPublishValue
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignResume
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSample
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSampleCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSaved
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignStep
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignZero
import VerifiedGarbage.Proof.Dsa.X86_64.RangeCT
import VerifiedGarbage.Proof.Dsa.X86_64.RangeHead
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyJoint
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyMinusCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyRangeCT
import VerifiedGarbage.Proof.Dsa.X86_64.Reduce
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInit
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceLoop
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceReadCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceStepCT
import VerifiedGarbage.Proof.Dsa.X86_64.Result
import VerifiedGarbage.Proof.Dsa.X86_64.Save
import VerifiedGarbage.Proof.Dsa.X86_64.ScanField
import VerifiedGarbage.Proof.Dsa.X86_64.ScanFieldCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleAddCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCheckCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleJointCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
import VerifiedGarbage.Proof.Dsa.X86_64.SealChild
import VerifiedGarbage.Proof.Dsa.X86_64.Sequences
import VerifiedGarbage.Proof.Dsa.X86_64.Setup
import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
import VerifiedGarbage.Proof.Dsa.X86_64.ShapeSizesCT
import VerifiedGarbage.Proof.Dsa.X86_64.SignificantLoop
import VerifiedGarbage.Proof.Dsa.X86_64.SigningABIPost
import VerifiedGarbage.Proof.Dsa.X86_64.SigningABIPre
import VerifiedGarbage.Proof.Dsa.X86_64.SigningCT
import VerifiedGarbage.Proof.Dsa.X86_64.SigningMain
import VerifiedGarbage.Proof.Dsa.X86_64.SigningOperands
import VerifiedGarbage.Proof.Dsa.X86_64.SigningReadyCT
import VerifiedGarbage.Proof.Dsa.X86_64.SigningVerified
import VerifiedGarbage.Proof.Dsa.X86_64.Store
import VerifiedGarbage.Proof.Dsa.X86_64.StoreSuffix
import VerifiedGarbage.Proof.Dsa.X86_64.TopMask
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyFailure
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingABIPost
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingABIPre
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingCT
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingMain
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingOperands
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingReadyCT
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingVerified
import VerifiedGarbage.Proof.Dsa.X86_64.WidthMask
import VerifiedGarbage.Proof.Dsa.X86_64.WorkspaceReady
import VerifiedGarbage.Proof.Dsa.X86_64.WriteScalarCT
import VerifiedGarbage.Proof.Dsa.X86_64.WriteSignature
import VerifiedGarbage.Proof.Dsa.X86_64.ZeroMask
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.RsaPss.Params
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.Derive
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.DomainWidths
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Dsa.PackedBytes
meta import VerifiedGarbage.Proof.Dsa.Random
meta import VerifiedGarbage.Proof.Dsa.RandomEncoding
meta import VerifiedGarbage.Proof.Dsa.RandomSign
meta import VerifiedGarbage.Proof.Dsa.RandomSignResult
meta import VerifiedGarbage.Proof.Dsa.RandomSignTrace
meta import VerifiedGarbage.Proof.Dsa.RandomTrace
meta import VerifiedGarbage.Proof.Dsa.RandomTraceResult
meta import VerifiedGarbage.Proof.Dsa.SignVerify
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Dsa.X86_64.AcceptedSpec
meta import VerifiedGarbage.Proof.Dsa.X86_64.Add
meta import VerifiedGarbage.Proof.Dsa.X86_64.AddCallCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.BufferFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.CTBlocks
meta import VerifiedGarbage.Proof.Dsa.X86_64.Call2
meta import VerifiedGarbage.Proof.Dsa.X86_64.CallAddCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.CallOperands
meta import VerifiedGarbage.Proof.Dsa.X86_64.Child
meta import VerifiedGarbage.Proof.Dsa.X86_64.CopyMasked
meta import VerifiedGarbage.Proof.Dsa.X86_64.DeriveCopy
meta import VerifiedGarbage.Proof.Dsa.X86_64.DeriveFailure
meta import VerifiedGarbage.Proof.Dsa.X86_64.DeriveMainCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.DeriveVerified
meta import VerifiedGarbage.Proof.Dsa.X86_64.DomainShapeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
meta import VerifiedGarbage.Proof.Dsa.X86_64.EnterLeave
meta import VerifiedGarbage.Proof.Dsa.X86_64.EntryFieldsFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
meta import VerifiedGarbage.Proof.Dsa.X86_64.Exponent
meta import VerifiedGarbage.Proof.Dsa.X86_64.Failure
meta import VerifiedGarbage.Proof.Dsa.X86_64.KeyPointers
meta import VerifiedGarbage.Proof.Dsa.X86_64.Load
meta import VerifiedGarbage.Proof.Dsa.X86_64.Masks
meta import VerifiedGarbage.Proof.Dsa.X86_64.Minus
meta import VerifiedGarbage.Proof.Dsa.X86_64.MinusStep
meta import VerifiedGarbage.Proof.Dsa.X86_64.Multiply
meta import VerifiedGarbage.Proof.Dsa.X86_64.OneScanCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.OrWords
meta import VerifiedGarbage.Proof.Dsa.X86_64.ParametersVerified
meta import VerifiedGarbage.Proof.Dsa.X86_64.Parent
meta import VerifiedGarbage.Proof.Dsa.X86_64.Parity
meta import VerifiedGarbage.Proof.Dsa.X86_64.Power
meta import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicKeyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicPrefix
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicSlices
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomBorrow
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopy
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyCandidate
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyInit
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyWhole
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomDraw
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawCheckCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawCopy
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawFinishCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawRange
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomFunctional
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomInRange
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomNonceEncoding
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomPrepare
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomPrepareFinish
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomPrepareState
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomRange
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSample
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleAgreement
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleLoop
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleLoopCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomScan
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignArgsSaved
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignAttempt
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignAttemptCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignBody
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallGeometry
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallMemory
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallObserve
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallPre
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallRetry
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallValue
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCode
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFinish
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignInit
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignInvalid
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignPublishValue
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignResume
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSample
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSampleCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSaved
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSingleCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignStep
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignZero
meta import VerifiedGarbage.Proof.Dsa.X86_64.RangeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RangeHead
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReadyJoint
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReadyMinusCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReadyRangeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Reduce
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInit
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceLoop
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceReadCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceStepCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Result
meta import VerifiedGarbage.Proof.Dsa.X86_64.Save
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScanField
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScanFieldCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleAddCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCheckCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleJointCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
meta import VerifiedGarbage.Proof.Dsa.X86_64.SealChild
meta import VerifiedGarbage.Proof.Dsa.X86_64.Sequences
meta import VerifiedGarbage.Proof.Dsa.X86_64.Setup
meta import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ShapeSizesCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.SignificantLoop
meta import VerifiedGarbage.Proof.Dsa.X86_64.SigningABIPost
meta import VerifiedGarbage.Proof.Dsa.X86_64.SigningABIPre
meta import VerifiedGarbage.Proof.Dsa.X86_64.SigningCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.SigningMain
meta import VerifiedGarbage.Proof.Dsa.X86_64.SigningOperands
meta import VerifiedGarbage.Proof.Dsa.X86_64.SigningReadyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.SigningVerified
meta import VerifiedGarbage.Proof.Dsa.X86_64.Store
meta import VerifiedGarbage.Proof.Dsa.X86_64.StoreSuffix
meta import VerifiedGarbage.Proof.Dsa.X86_64.TopMask
meta import VerifiedGarbage.Proof.Dsa.X86_64.VerifyFailure
meta import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingABIPost
meta import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingABIPre
meta import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingMain
meta import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingOperands
meta import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingReadyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingVerified
meta import VerifiedGarbage.Proof.Dsa.X86_64.WidthMask
meta import VerifiedGarbage.Proof.Dsa.X86_64.WorkspaceReady
meta import VerifiedGarbage.Proof.Dsa.X86_64.WriteScalarCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.WriteSignature
meta import VerifiedGarbage.Proof.Dsa.X86_64.ZeroMask
meta import VerifiedGarbage.Proof.Dsa.Zero
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.CallSp
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.RsaPss.Params

/-! Compose initialization, retries, and publication for valid subgroup moduli. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem random_sign_init_agreement {extra : Nat} {s t : State}
    (hs : RandomSignABI extra s) (ht : RandomSignABI extra t) (hp : RandomSignPublicAgree s t)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (.seq (.block RandomSign.entry) Random.prepare) (allocState Random.frameBytes s) tsa u)
    (eb : Exec isa (.seq (.block RandomSign.entry) Random.prepare) (allocState Random.frameBytes t) tsb w) : tsa = tsb := by
  have he : (⟨randomBase s, s.gpr .rcx + s.gpr .r9, randomQBytes s⟩ : RandomPreparePublic) =
      ⟨randomBase t, t.gpr .rcx + t.gpr .r9, randomQBytes t⟩ := by
    rw [hp.base, hp.regs .rcx (by decide), hp.regs .r9 (by decide), hp.qbytes]
  exact (random_sign_init_ct _ _ _ _ _ _
    ⟨_, ⟨s, extra, hs, rfl, rfl⟩, t, extra, ht, rfl, he⟩ ea eb).1

theorem random_sign_cmp_zero_ct : RelCT isa (fun _ _ => True) (.block [.alu .cmp .rax (.imm 0)]) (fun _ _ => True) := by
  exact (two_taint (Φ := fun (_ : Unit) (_ : State) => True) []
    (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)).mono
    (fun _ _ _ => ⟨(), trivial, trivial⟩) (fun _ _ _ => trivial)

private theorem test_zero_mx {s : State} :
    WP isa (.block [.alu .cmp .rax (.imm 0)]) s fun t =>
      ((t.mem = s.mem ∧ t.zf = some (s.gpr .rax == 0)) ∧ Keep [.rax] s t) ∧ t.mxcsr = s.mxcsr :=
  WP.mono_mx (by decide) random_sign_test_zero (fun _ h hm => ⟨h, hm⟩)

def randomSignTail (v : Backend) : Prog isa :=
  .seq (.block [.alu .cmp .rax (.imm 0)])
    (.seq (.ite .e (.block [.store (Random.sp Random.oStatus) .rax])
      (.loop (.seq (RandomSign.attempt (randomSignerName v) (SignVerify.sign v.sq v.mul)) randomSignStatusTest) .e)) RandomSign.finish)

private theorem valid_tail (v : Backend) {s t a b : State}
    {hs : RandomSignABI v.stack s} {ht : RandomSignABI v.stack t}
    {hqs : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {hqt : 1 < Spec.Dsa.decodeBE (randomQBytes t)}
    (ha : RandomSignRunning hs hqs 0 8 a) (hb : RandomSignRunning ht hqt 0 8 b)
    (hra : a.gpr .rax = 1) (hrb : b.gpr .rax = 1) (hp : RandomSignPublicAgree s t)
    (htrace : (randomSignRemaining (randomInput s) 0 8).trace = (randomSignRemaining (randomInput t) 0 8).trace)
    (hstatus : (randomSignRemaining (randomInput s) 0 8).status = (randomSignRemaining (randomInput t) 0 8).status)
    {tsa tsb : List Leak} {u w : State} (ea : Exec isa (randomSignTail v) a tsa u)
    (eb : Exec isa (randomSignTail v) b tsb w) : tsa = tsb := by
  cases ea with
  | seq eac ear => cases ear with
    | seq eai eaf =>
      cases eb with
      | seq ebc ebr => cases ebr with
        | seq ebi ebf =>
          have hcmp := (random_sign_cmp_zero_ct _ _ _ _ _ _ trivial eac ebc).1
          obtain ⟨⟨⟨ham, haz⟩, hka⟩, hmxa⟩ := random_post_of_exec test_zero_mx eac
          obtain ⟨⟨⟨hbm, hbz⟩, hkb⟩, hmxb⟩ := random_post_of_exec test_zero_mx ebc
          have har := ha.congr ham hka hmxa
          have hbr := hb.congr hbm hkb hmxb
          rw [hra] at haz
          rw [hrb] at hbz
          cases eai with
          | iteT hc _ => simp only [eval, haz] at hc; contradiction
          | iteF _ eal =>
            cases ebi with
            | iteT hc _ => simp only [eval, hbz] at hc; contradiction
            | iteF _ ebl =>
              have hloop := (random_sign_loop_ct v hp 8 _ _ _ _ _ _
                ⟨by decide, by decide, 0, har, hbr, htrace⟩ eal ebl).1
              obtain ⟨⟨_, hrunA⟩, hsta, _⟩ := random_post_of_exec (random_sign_loop_correct v har (by decide) (by decide)) eal
              obtain ⟨⟨_, hrunB⟩, hstb, _⟩ := random_post_of_exec (random_sign_loop_correct v hbr (by decide) (by decide)) ebl
              rw [← hstatus] at hstb
              have hfinish := random_finish_agreement hs ht hrunA.finishPre hrunB.finishPre hp hsta hstb eaf ebf
              rw [hcmp, hloop, hfinish]

theorem random_sign_body_valid_ct (v : Backend) {s t : State}
    (hs : RandomSignABI v.stack s) (ht : RandomSignABI v.stack t) (hp : RandomSignPublicAgree s t)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s))
    (htrace : (randomSignRemaining (randomInput s) 0 8).trace = (randomSignRemaining (randomInput t) 0 8).trace)
    (hstatus : (randomSignRemaining (randomInput s) 0 8).status = (randomSignRemaining (randomInput t) 0 8).status)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (RandomSign.body (randomSignerName v) (SignVerify.sign v.sq v.mul)) (allocState Random.frameBytes s) tsa u)
    (eb : Exec isa (RandomSign.body (randomSignerName v) (SignVerify.sign v.sq v.mul)) (allocState Random.frameBytes t) tsb w) : tsa = tsb := by
  have hqt : 1 < Spec.Dsa.decodeBE (randomQBytes t) := by rw [← hp.qbytes]; exact hq
  cases ea with
  | seq eae ear => cases ear with
    | seq eap eat =>
      cases eb with
      | seq ebe ebr => cases ebr with
        | seq ebp ebt =>
          have hinit := random_sign_init_agreement hs ht hp (.seq eae eap) (.seq ebe ebp)
          obtain ⟨hra, har⟩ := random_post_of_exec (random_sign_init_running hs hq) (.seq eae eap)
          obtain ⟨hrb, hbr⟩ := random_post_of_exec (random_sign_init_running ht hqt) (.seq ebe ebp)
          have htail := valid_tail v har hbr hra hrb hp htrace hstatus eat ebt
          rw [← List.append_assoc, ← List.append_assoc, hinit, htail]

end VG.Proof.Dsa.X86_64
