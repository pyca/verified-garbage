module
public import VerifiedGarbage.Impl.Dsa.AArch64.GenerateKey
public import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.AcceptedSpec
import VerifiedGarbage.Proof.Dsa.AArch64.Add
import VerifiedGarbage.Proof.Dsa.AArch64.AddCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.Arithmetic
import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
import VerifiedGarbage.Proof.Dsa.AArch64.BufferFrame
import VerifiedGarbage.Proof.Dsa.AArch64.CTBlocks
import VerifiedGarbage.Proof.Dsa.AArch64.Call2
import VerifiedGarbage.Proof.Dsa.AArch64.CallAddCT
import VerifiedGarbage.Proof.Dsa.AArch64.CallOperands
import VerifiedGarbage.Proof.Dsa.AArch64.Child
import VerifiedGarbage.Proof.Dsa.AArch64.CopyMasked
import VerifiedGarbage.Proof.Dsa.AArch64.DeriveCopy
import VerifiedGarbage.Proof.Dsa.AArch64.DeriveFailure
import VerifiedGarbage.Proof.Dsa.AArch64.DeriveMainCT
import VerifiedGarbage.Proof.Dsa.AArch64.DeriveVerified
import VerifiedGarbage.Proof.Dsa.AArch64.DomainShapeCT
import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
import VerifiedGarbage.Proof.Dsa.AArch64.EntryCT
import VerifiedGarbage.Proof.Dsa.AArch64.EntryFieldsFrame
import VerifiedGarbage.Proof.Dsa.AArch64.EntryScratch
import VerifiedGarbage.Proof.Dsa.AArch64.Failure
import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyBody
import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyCorrect
import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyDeriveCall
import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyDerivePre
import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyDeriveStep
import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeySampled
import VerifiedGarbage.Proof.Dsa.AArch64.KeyPointers
import VerifiedGarbage.Proof.Dsa.AArch64.Load
import VerifiedGarbage.Proof.Dsa.AArch64.LowerScan
import VerifiedGarbage.Proof.Dsa.AArch64.Masks
import VerifiedGarbage.Proof.Dsa.AArch64.Minus
import VerifiedGarbage.Proof.Dsa.AArch64.MinusCore
import VerifiedGarbage.Proof.Dsa.AArch64.ModulusMinus
import VerifiedGarbage.Proof.Dsa.AArch64.Multiply
import VerifiedGarbage.Proof.Dsa.AArch64.NewChild
import VerifiedGarbage.Proof.Dsa.AArch64.OneScanCT
import VerifiedGarbage.Proof.Dsa.AArch64.ParametersVerified
import VerifiedGarbage.Proof.Dsa.AArch64.Parent
import VerifiedGarbage.Proof.Dsa.AArch64.Parity
import VerifiedGarbage.Proof.Dsa.AArch64.Power
import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
import VerifiedGarbage.Proof.Dsa.AArch64.PublicKeyCT
import VerifiedGarbage.Proof.Dsa.AArch64.PublicPrefix
import VerifiedGarbage.Proof.Dsa.AArch64.PublicSlices
import VerifiedGarbage.Proof.Dsa.AArch64.RandomBorrow
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopy
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopyCandidate
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopyInit
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopyWhole
import VerifiedGarbage.Proof.Dsa.AArch64.RandomDraw
import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawCopy
import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawRange
import VerifiedGarbage.Proof.Dsa.AArch64.RandomFrame
import VerifiedGarbage.Proof.Dsa.AArch64.RandomFunctional
import VerifiedGarbage.Proof.Dsa.AArch64.RandomInRange
import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
import VerifiedGarbage.Proof.Dsa.AArch64.RandomNonceEncoding
import VerifiedGarbage.Proof.Dsa.AArch64.RandomPrepare
import VerifiedGarbage.Proof.Dsa.AArch64.RandomPrepareFinish
import VerifiedGarbage.Proof.Dsa.AArch64.RandomPrepareState
import VerifiedGarbage.Proof.Dsa.AArch64.RandomRange
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSample
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSampleLoop
import VerifiedGarbage.Proof.Dsa.AArch64.RandomScan
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignArgsSaved
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignAttempt
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignBody
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallMemory
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallObserve
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallPre
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallRetry
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallValue
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCode
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinish
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignInit
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignInvalid
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignPublishValue
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignResume
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSample
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSaved
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSingleCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignZero
import VerifiedGarbage.Proof.Dsa.AArch64.RangeCT
import VerifiedGarbage.Proof.Dsa.AArch64.RangeMask
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyJoint
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyMinusCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyRangeCT
import VerifiedGarbage.Proof.Dsa.AArch64.Reduce
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceCount
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceInit
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceLoop
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceRead
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceReadCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceSetup
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceStepCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReleaseBytes
import VerifiedGarbage.Proof.Dsa.AArch64.Result
import VerifiedGarbage.Proof.Dsa.AArch64.ResultCall
import VerifiedGarbage.Proof.Dsa.AArch64.ScanField
import VerifiedGarbage.Proof.Dsa.AArch64.ScanFieldCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleAddCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCheckCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
import VerifiedGarbage.Proof.Dsa.AArch64.Sequences
import VerifiedGarbage.Proof.Dsa.AArch64.Setup
import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
import VerifiedGarbage.Proof.Dsa.AArch64.ShapeSizesCT
import VerifiedGarbage.Proof.Dsa.AArch64.SignificantLoop
import VerifiedGarbage.Proof.Dsa.AArch64.SigningABIPost
import VerifiedGarbage.Proof.Dsa.AArch64.SigningABIPre
import VerifiedGarbage.Proof.Dsa.AArch64.SigningCT
import VerifiedGarbage.Proof.Dsa.AArch64.SigningMain
import VerifiedGarbage.Proof.Dsa.AArch64.SigningOperands
import VerifiedGarbage.Proof.Dsa.AArch64.SigningReadyCT
import VerifiedGarbage.Proof.Dsa.AArch64.SigningVerified
import VerifiedGarbage.Proof.Dsa.AArch64.Store
import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
import VerifiedGarbage.Proof.Dsa.AArch64.TopMask
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingABIPost
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingABIPre
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingCT
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingMain
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingOperands
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingReadyCT
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingVerified
import VerifiedGarbage.Proof.Dsa.AArch64.WidthMask
import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady
import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalar
import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalarCT
import VerifiedGarbage.Proof.Dsa.AArch64.WriteSignature
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
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
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.RsaPss.Params
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Double
meta import VerifiedGarbage.Proof.Bignum.AArch64.Mont
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Bignum.AArch64.Setup
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.Store
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Dsa.AArch64.AcceptedSpec
meta import VerifiedGarbage.Proof.Dsa.AArch64.Add
meta import VerifiedGarbage.Proof.Dsa.AArch64.AddCallCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.BufferFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.CTBlocks
meta import VerifiedGarbage.Proof.Dsa.AArch64.Call2
meta import VerifiedGarbage.Proof.Dsa.AArch64.CallAddCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.CallOperands
meta import VerifiedGarbage.Proof.Dsa.AArch64.Child
meta import VerifiedGarbage.Proof.Dsa.AArch64.CopyMasked
meta import VerifiedGarbage.Proof.Dsa.AArch64.DeriveCopy
meta import VerifiedGarbage.Proof.Dsa.AArch64.DeriveFailure
meta import VerifiedGarbage.Proof.Dsa.AArch64.DeriveMainCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.DeriveVerified
meta import VerifiedGarbage.Proof.Dsa.AArch64.DomainShapeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
meta import VerifiedGarbage.Proof.Dsa.AArch64.EntryCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.EntryFieldsFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.EntryScratch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Failure
meta import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyBody
meta import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyCallCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyCorrect
meta import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyDeriveCall
meta import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyDerivePre
meta import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyDeriveStep
meta import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeySampled
meta import VerifiedGarbage.Proof.Dsa.AArch64.KeyPointers
meta import VerifiedGarbage.Proof.Dsa.AArch64.Load
meta import VerifiedGarbage.Proof.Dsa.AArch64.LowerScan
meta import VerifiedGarbage.Proof.Dsa.AArch64.Masks
meta import VerifiedGarbage.Proof.Dsa.AArch64.Minus
meta import VerifiedGarbage.Proof.Dsa.AArch64.MinusCore
meta import VerifiedGarbage.Proof.Dsa.AArch64.ModulusMinus
meta import VerifiedGarbage.Proof.Dsa.AArch64.Multiply
meta import VerifiedGarbage.Proof.Dsa.AArch64.NewChild
meta import VerifiedGarbage.Proof.Dsa.AArch64.OneScanCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ParametersVerified
meta import VerifiedGarbage.Proof.Dsa.AArch64.Parent
meta import VerifiedGarbage.Proof.Dsa.AArch64.Parity
meta import VerifiedGarbage.Proof.Dsa.AArch64.Power
meta import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicKeyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicPrefix
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicSlices
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomBorrow
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopy
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopyCandidate
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopyInit
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopyWhole
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomDraw
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawCopy
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawRange
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomFunctional
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomInRange
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomNonceEncoding
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomPrepare
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomPrepareFinish
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomPrepareState
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomRange
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSample
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSampleLoop
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomScan
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignArgsSaved
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignAttempt
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignBody
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallMemory
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallObserve
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallPre
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallRetry
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallValue
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCode
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinish
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignInit
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignInvalid
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignPublishValue
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignResume
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSample
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSaved
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSingleCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignZero
meta import VerifiedGarbage.Proof.Dsa.AArch64.RangeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RangeMask
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReadyJoint
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReadyMinusCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReadyRangeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Reduce
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceCount
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceInit
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceLoop
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceRead
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceReadCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceSetup
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceStepCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReleaseBytes
meta import VerifiedGarbage.Proof.Dsa.AArch64.Result
meta import VerifiedGarbage.Proof.Dsa.AArch64.ResultCall
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScanField
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScanFieldCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleAddCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCheckCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
meta import VerifiedGarbage.Proof.Dsa.AArch64.Sequences
meta import VerifiedGarbage.Proof.Dsa.AArch64.Setup
meta import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ShapeSizesCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.SignificantLoop
meta import VerifiedGarbage.Proof.Dsa.AArch64.SigningABIPost
meta import VerifiedGarbage.Proof.Dsa.AArch64.SigningABIPre
meta import VerifiedGarbage.Proof.Dsa.AArch64.SigningCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.SigningMain
meta import VerifiedGarbage.Proof.Dsa.AArch64.SigningOperands
meta import VerifiedGarbage.Proof.Dsa.AArch64.SigningReadyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.SigningVerified
meta import VerifiedGarbage.Proof.Dsa.AArch64.Store
meta import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
meta import VerifiedGarbage.Proof.Dsa.AArch64.TopMask
meta import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingABIPost
meta import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingABIPre
meta import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingMain
meta import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingOperands
meta import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingReadyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingVerified
meta import VerifiedGarbage.Proof.Dsa.AArch64.WidthMask
meta import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady
meta import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalar
meta import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalarCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.WriteSignature
meta import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
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
meta import VerifiedGarbage.Proof.Dsa.Zero
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.RsaPss.Params

/-! # Key generation's straight-line pieces: only the stack pointer is public in them -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem keygen_head_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block (GenerateKey.entry ++ GenerateKey.checkArgs)) (fun _ _ => True) :=
  (two_taint (Φ := fun (B : Addr) s => s.sp = B) [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)).mono
    (fun s _ h => ⟨s.sp, rfl, h.symm, h⟩) (fun _ _ _ => trivial)

theorem keygen_testCheck_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block [.ldrSp .x30 RandomSign.oLink, .logic .orr .w .x0 .x0 .x0]) (fun _ _ => True) :=
  (two_taint (Φ := fun (B : Addr) s => s.sp = B) [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)).mono
    (fun s _ h => ⟨s.sp, rfl, h.symm, h⟩) (fun _ _ _ => trivial)

theorem keygen_storeStatus_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block (Random.store Random.oStatus .x0 ++ ([.subImm .x .x4 .x0 1] : List Instr))) (fun _ _ => True) :=
  (two_taint (Φ := fun (B : Addr) s => s.sp = B) [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)).mono
    (fun s _ h => ⟨s.sp, rfl, h.symm, h⟩) (fun _ _ _ => trivial)

theorem keygen_deriveArgs_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block GenerateKey.deriveArgs) (fun _ _ => True) :=
  (two_taint (Φ := fun (B : Addr) s => s.sp = B) [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)).mono
    (fun s _ h => ⟨s.sp, rfl, h.symm, h⟩) (fun _ _ _ => trivial)

theorem keygen_keepStatus_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block GenerateKey.keepStatus) (fun _ _ => True) :=
  (two_taint (Φ := fun (B : Addr) s => s.sp = B) [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)).mono
    (fun s _ h => ⟨s.sp, rfl, h.symm, h⟩) (fun _ _ _ => trivial)

end VG.Proof.Dsa.AArch64
