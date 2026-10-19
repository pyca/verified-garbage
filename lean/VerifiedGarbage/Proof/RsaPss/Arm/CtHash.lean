module
public import VerifiedGarbage.Proof.RsaPss.Arm.CtBase

public import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPss.Arm.CtPad
import VerifiedGarbage.Proof.RsaPss.Arm.CtInit
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesGcm.Arm.Compare
public import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
public import VerifiedGarbage.Proof.AesGcm.Arm.Entry
public import VerifiedGarbage.Proof.AesGcm.Arm.Ghash1
public import VerifiedGarbage.Proof.Bignum.Arm.ActivateWorkspace
public import VerifiedGarbage.Proof.Bignum.Arm.AddCarry
public import VerifiedGarbage.Proof.Bignum.Arm.ArgsCT
public import VerifiedGarbage.Proof.Bignum.Arm.ArrayFrame
public import VerifiedGarbage.Proof.Bignum.Arm.BasesTail
public import VerifiedGarbage.Proof.Bignum.Arm.ByteWords
public import VerifiedGarbage.Proof.Bignum.Arm.CompareBuffer
public import VerifiedGarbage.Proof.Bignum.Arm.CompareByteStep
public import VerifiedGarbage.Proof.Bignum.Arm.CompareBytes
public import VerifiedGarbage.Proof.Bignum.Arm.CompareBytesCT
public import VerifiedGarbage.Proof.Bignum.Arm.CopyBuffer
public import VerifiedGarbage.Proof.Bignum.Arm.CopyByteStep
public import VerifiedGarbage.Proof.Bignum.Arm.CopyBytesCT
public import VerifiedGarbage.Proof.Bignum.Arm.CopyRegion
public import VerifiedGarbage.Proof.Bignum.Arm.CrtAdvanceLink
public import VerifiedGarbage.Proof.Bignum.Arm.CrtEnterPrime
public import VerifiedGarbage.Proof.Bignum.Arm.CrtInitialize
public import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
public import VerifiedGarbage.Proof.Bignum.Arm.CrtLeavePrime
public import VerifiedGarbage.Proof.Bignum.Arm.CrtLinkStep
public import VerifiedGarbage.Proof.Bignum.Arm.CrtLinks
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPrepare
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimeArgs
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimeEnter
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSaveMain
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupAll
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupFrame
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupMain
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupPrime
public import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
public import VerifiedGarbage.Proof.Bignum.Arm.CrtStrides
public import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceCall
public import VerifiedGarbage.Proof.Bignum.Arm.CsubCT
public import VerifiedGarbage.Proof.Bignum.Arm.CsubValue
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleBody
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleCore
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleCountMemory
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleFnBody
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleFnRestore
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoop
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopBody
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopSteps
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleProduct
public import VerifiedGarbage.Proof.Bignum.Arm.ExportArray
public import VerifiedGarbage.Proof.Bignum.Arm.ExportArrayArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ExportEncoding
public import VerifiedGarbage.Proof.Bignum.Arm.FinishArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ImportModulus
public import VerifiedGarbage.Proof.Bignum.Arm.ImportOperandLayout
public import VerifiedGarbage.Proof.Bignum.Arm.InitInverse
public import VerifiedGarbage.Proof.Bignum.Arm.InitMetaMemory
public import VerifiedGarbage.Proof.Bignum.Arm.InverseArgs
public import VerifiedGarbage.Proof.Bignum.Arm.InverseReady
public import VerifiedGarbage.Proof.Bignum.Arm.KeepsBridge
public import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
public import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
public import VerifiedGarbage.Proof.Bignum.Arm.LayoutExternal
public import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
public import VerifiedGarbage.Proof.Bignum.Arm.LoadArray
public import VerifiedGarbage.Proof.Bignum.Arm.LoadBE
public import VerifiedGarbage.Proof.Bignum.Arm.LoadBEArgs
public import VerifiedGarbage.Proof.Bignum.Arm.LoadBEFn
public import VerifiedGarbage.Proof.Bignum.Arm.LoadBEFnArgs
public import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
public import VerifiedGarbage.Proof.Bignum.Arm.MaskByteStep
public import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
public import VerifiedGarbage.Proof.Bignum.Arm.MaskOutput
public import VerifiedGarbage.Proof.Bignum.Arm.MaskOutputArgs
public import VerifiedGarbage.Proof.Bignum.Arm.Minv64
public import VerifiedGarbage.Proof.Bignum.Arm.Minv64Steps
public import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
public import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckBounds
public import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckCalc
public import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckFinish
public import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckMath
public import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckRead
public import VerifiedGarbage.Proof.Bignum.Arm.ModulusReady
public import VerifiedGarbage.Proof.Bignum.Arm.MontBody
public import VerifiedGarbage.Proof.Bignum.Arm.MontCore
public import VerifiedGarbage.Proof.Bignum.Arm.MontFinish
public import VerifiedGarbage.Proof.Bignum.Arm.MontFnBody
public import VerifiedGarbage.Proof.Bignum.Arm.MontInitCT
public import VerifiedGarbage.Proof.Bignum.Arm.MontMath
public import VerifiedGarbage.Proof.Bignum.Arm.MontOpArgs
public import VerifiedGarbage.Proof.Bignum.Arm.MontRounds
public import VerifiedGarbage.Proof.Bignum.Arm.MontRoundsCT
public import VerifiedGarbage.Proof.Bignum.Arm.Mul64
public import VerifiedGarbage.Proof.Bignum.Arm.Mul64Math
public import VerifiedGarbage.Proof.Bignum.Arm.Newton64Math
public import VerifiedGarbage.Proof.Bignum.Arm.Newton64Steps
public import VerifiedGarbage.Proof.Bignum.Arm.PcBody
public import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
public import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
public import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
public import VerifiedGarbage.Proof.Bignum.Arm.PcEntryMemory
public import VerifiedGarbage.Proof.Bignum.Arm.PcEntryReady
public import VerifiedGarbage.Proof.Bignum.Arm.PcFail
public import VerifiedGarbage.Proof.Bignum.Arm.PcFailArgs
public import VerifiedGarbage.Proof.Bignum.Arm.PcHead
public import VerifiedGarbage.Proof.Bignum.Arm.PcValid
public import VerifiedGarbage.Proof.Bignum.Arm.Precompute
public import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeInverse
public import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOut
public import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOutArgs
public import VerifiedGarbage.Proof.Bignum.Arm.PrepareZero
public import VerifiedGarbage.Proof.Bignum.Arm.ProductArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ProductStage
public import VerifiedGarbage.Proof.Bignum.Arm.QuotientStage
public import VerifiedGarbage.Proof.Bignum.Arm.R2
public import VerifiedGarbage.Proof.Bignum.Arm.R2Constants
public import VerifiedGarbage.Proof.Bignum.Arm.R2CountInit
public import VerifiedGarbage.Proof.Bignum.Arm.R2Init
public import VerifiedGarbage.Proof.Bignum.Arm.ReduceChoice
public import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ReductionStage
public import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
public import VerifiedGarbage.Proof.Bignum.Arm.RestoreSlots
public import VerifiedGarbage.Proof.Bignum.Arm.ReverseByteStep
public import VerifiedGarbage.Proof.Bignum.Arm.ReverseEncoding
public import VerifiedGarbage.Proof.Bignum.Arm.ReverseRegion
public import VerifiedGarbage.Proof.Bignum.Arm.Round
public import VerifiedGarbage.Proof.Bignum.Arm.RoundFinish
public import VerifiedGarbage.Proof.Bignum.Arm.RoundFinishMemory
public import VerifiedGarbage.Proof.Bignum.Arm.RoundFinishSteps
public import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
public import VerifiedGarbage.Proof.Bignum.Arm.Row
public import VerifiedGarbage.Proof.Bignum.Arm.RowAdvance
public import VerifiedGarbage.Proof.Bignum.Arm.RowBody
public import VerifiedGarbage.Proof.Bignum.Arm.RowBody2
public import VerifiedGarbage.Proof.Bignum.Arm.RowCarry
public import VerifiedGarbage.Proof.Bignum.Arm.RowCarryMemory
public import VerifiedGarbage.Proof.Bignum.Arm.RowFull
public import VerifiedGarbage.Proof.Bignum.Arm.RowFullCT
public import VerifiedGarbage.Proof.Bignum.Arm.RowStep
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeBit
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulus
public import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandArgs
public import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandLayout
public import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasBody
public import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasRow
public import VerifiedGarbage.Proof.Bignum.Arm.SelectArray
public import VerifiedGarbage.Proof.Bignum.Arm.SelectArrayArgs
public import VerifiedGarbage.Proof.Bignum.Arm.SelectBody
public import VerifiedGarbage.Proof.Bignum.Arm.SelectCT
public import VerifiedGarbage.Proof.Bignum.Arm.SelectPrepare
public import VerifiedGarbage.Proof.Bignum.Arm.SelectRow
public import VerifiedGarbage.Proof.Bignum.Arm.SelectStep
public import VerifiedGarbage.Proof.Bignum.Arm.SelectWord
public import VerifiedGarbage.Proof.Bignum.Arm.SetBaseStep
public import VerifiedGarbage.Proof.Bignum.Arm.SetBases
public import VerifiedGarbage.Proof.Bignum.Arm.SetSmall
public import VerifiedGarbage.Proof.Bignum.Arm.SetSmallArgs
public import VerifiedGarbage.Proof.Bignum.Arm.SetSmallCT
public import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
public import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFnCT
public import VerifiedGarbage.Proof.Bignum.Arm.Setup
public import VerifiedGarbage.Proof.Bignum.Arm.SetupArgs
public import VerifiedGarbage.Proof.Bignum.Arm.SetupFrame
public import VerifiedGarbage.Proof.Bignum.Arm.Shift
public import VerifiedGarbage.Proof.Bignum.Arm.ShiftArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ShiftCT
public import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeft
public import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeftStep
public import VerifiedGarbage.Proof.Bignum.Arm.ShiftStep
public import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
public import VerifiedGarbage.Proof.Bignum.Arm.SmallConstLayout
public import VerifiedGarbage.Proof.Bignum.Arm.SmallConstLayoutCT
public import VerifiedGarbage.Proof.Bignum.Arm.SquareBody
public import VerifiedGarbage.Proof.Bignum.Arm.SquareCross
public import VerifiedGarbage.Proof.Bignum.Arm.SquareFinish
public import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
public import VerifiedGarbage.Proof.Bignum.Arm.Stack
public import VerifiedGarbage.Proof.Bignum.Arm.StackCT
public import VerifiedGarbage.Proof.Bignum.Arm.StackPair
public import VerifiedGarbage.Proof.Bignum.Arm.Store64
public import VerifiedGarbage.Proof.Bignum.Arm.Sub
public import VerifiedGarbage.Proof.Bignum.Arm.Sub64
public import VerifiedGarbage.Proof.Bignum.Arm.Sub64Math
public import VerifiedGarbage.Proof.Bignum.Arm.SubAdvance
public import VerifiedGarbage.Proof.Bignum.Arm.SubBody
public import VerifiedGarbage.Proof.Bignum.Arm.SubRow
public import VerifiedGarbage.Proof.Bignum.Arm.SubStep
public import VerifiedGarbage.Proof.Bignum.Arm.WideMath
public import VerifiedGarbage.Proof.Bignum.Arm.WideValue
public import VerifiedGarbage.Proof.Bignum.Arm.ZeroStep
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Cmac.Mem
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Arm.Bytes
public import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Framework.Arm.TaintErase
public import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.OffsetBelow
public import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Proof.MdStream.Arm.Words
public import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Pbkdf2.Memory
public import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
public import VerifiedGarbage.Proof.Rc2.Memory32
public import VerifiedGarbage.Proof.Rc2.PairMem
public import VerifiedGarbage.Proof.Rsa.AcceptanceMask32
public import VerifiedGarbage.Proof.Rsa.Arm.PrivAllocCT
public import VerifiedGarbage.Proof.Rsa.Arm.PrivArgsCT
public import VerifiedGarbage.Proof.Rsa.Arm.PrivBody
public import VerifiedGarbage.Proof.Rsa.Arm.PrivBodyCT
public import VerifiedGarbage.Proof.Rsa.Arm.PrivCallPublic
public import VerifiedGarbage.Proof.Rsa.Arm.PrivCallsCT
public import VerifiedGarbage.Proof.Rsa.Arm.PrivCheck
public import VerifiedGarbage.Proof.Rsa.Arm.PrivCheckFrame
public import VerifiedGarbage.Proof.Rsa.Arm.PrivCheckLogic
public import VerifiedGarbage.Proof.Rsa.Arm.PrivCopyArgs
public import VerifiedGarbage.Proof.Rsa.Arm.PrivCopyIncoming
public import VerifiedGarbage.Proof.Rsa.Arm.PrivCopyRetained
public import VerifiedGarbage.Proof.Rsa.Arm.PrivCrtCall
public import VerifiedGarbage.Proof.Rsa.Arm.PrivMask
public import VerifiedGarbage.Proof.Rsa.Arm.PrivPdCall
public import VerifiedGarbage.Proof.Rsa.Arm.PrivPdSuffix
public import VerifiedGarbage.Proof.Rsa.Arm.PrivPreWords
public import VerifiedGarbage.Proof.Rsa.Arm.PrivRegions
public import VerifiedGarbage.Proof.Rsa.Arm.PrivRelease
public import VerifiedGarbage.Proof.Rsa.Arm.PrivReleaseArgs
public import VerifiedGarbage.Proof.Rsa.Arm.PrivReleaseBuffer
public import VerifiedGarbage.Proof.Rsa.Arm.PrivReleaseCT
public import VerifiedGarbage.Proof.Rsa.Arm.PrivReleaseStep
public import VerifiedGarbage.Proof.Rsa.Arm.PrivSaveIncoming
public import VerifiedGarbage.Proof.Rsa.Arm.PrivSaveRegs
public import VerifiedGarbage.Proof.Rsa.Arm.PrivSaveResult
public import VerifiedGarbage.Proof.Rsa.Arm.PrivStackWord
public import VerifiedGarbage.Proof.Rsa.Arm.PrivStatusPreserved
public import VerifiedGarbage.Proof.Rsa.Arm.PrivStoreTemporary
public import VerifiedGarbage.Proof.Rsa.Arm.PrivTailCT
public import VerifiedGarbage.Proof.Rsa.Arm.PrivTailContext
public import VerifiedGarbage.Proof.Rsa.Octets
public import VerifiedGarbage.Proof.Rsa.ZeroTest32
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
public import VerifiedGarbage.Proof.RsaPss.Arm.CtPad
public import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Proof.AesGcm.Arm.Compare
import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
import VerifiedGarbage.Proof.AesGcm.Arm.Entry
import VerifiedGarbage.Proof.AesGcm.Arm.Ghash1
import VerifiedGarbage.Proof.Bignum.Arm.ActivateWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.AddCarry
import VerifiedGarbage.Proof.Bignum.Arm.ArgsCT
import VerifiedGarbage.Proof.Bignum.Arm.ArrayFrame
import VerifiedGarbage.Proof.Bignum.Arm.BasesTail
import VerifiedGarbage.Proof.Bignum.Arm.ByteWords
import VerifiedGarbage.Proof.Bignum.Arm.CompareBuffer
import VerifiedGarbage.Proof.Bignum.Arm.CompareByteStep
import VerifiedGarbage.Proof.Bignum.Arm.CompareBytes
import VerifiedGarbage.Proof.Bignum.Arm.CompareBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.CopyBuffer
import VerifiedGarbage.Proof.Bignum.Arm.CopyByteStep
import VerifiedGarbage.Proof.Bignum.Arm.CopyBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.CopyRegion
import VerifiedGarbage.Proof.Bignum.Arm.CrtAdvanceLink
import VerifiedGarbage.Proof.Bignum.Arm.CrtEnterPrime
import VerifiedGarbage.Proof.Bignum.Arm.CrtInitialize
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Bignum.Arm.CrtLeavePrime
import VerifiedGarbage.Proof.Bignum.Arm.CrtLinkStep
import VerifiedGarbage.Proof.Bignum.Arm.CrtLinks
import VerifiedGarbage.Proof.Bignum.Arm.CrtPrepare
import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimeArgs
import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimeEnter
import VerifiedGarbage.Proof.Bignum.Arm.CrtSaveMain
import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupAll
import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupFrame
import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupMain
import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupPrime
import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Bignum.Arm.CrtStrides
import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceCall
import VerifiedGarbage.Proof.Bignum.Arm.CsubCT
import VerifiedGarbage.Proof.Bignum.Arm.CsubValue
import VerifiedGarbage.Proof.Bignum.Arm.DoubleBody
import VerifiedGarbage.Proof.Bignum.Arm.DoubleCore
import VerifiedGarbage.Proof.Bignum.Arm.DoubleCountMemory
import VerifiedGarbage.Proof.Bignum.Arm.DoubleFnBody
import VerifiedGarbage.Proof.Bignum.Arm.DoubleFnRestore
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoop
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopBody
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopSteps
import VerifiedGarbage.Proof.Bignum.Arm.DoubleProduct
import VerifiedGarbage.Proof.Bignum.Arm.ExportArray
import VerifiedGarbage.Proof.Bignum.Arm.ExportArrayArgs
import VerifiedGarbage.Proof.Bignum.Arm.ExportEncoding
import VerifiedGarbage.Proof.Bignum.Arm.FinishArgs
import VerifiedGarbage.Proof.Bignum.Arm.ImportModulus
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperandLayout
import VerifiedGarbage.Proof.Bignum.Arm.InitInverse
import VerifiedGarbage.Proof.Bignum.Arm.InitMetaMemory
import VerifiedGarbage.Proof.Bignum.Arm.InverseArgs
import VerifiedGarbage.Proof.Bignum.Arm.InverseReady
import VerifiedGarbage.Proof.Bignum.Arm.KeepsBridge
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
import VerifiedGarbage.Proof.Bignum.Arm.LayoutExternal
import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
import VerifiedGarbage.Proof.Bignum.Arm.LoadArray
import VerifiedGarbage.Proof.Bignum.Arm.LoadBE
import VerifiedGarbage.Proof.Bignum.Arm.LoadBEArgs
import VerifiedGarbage.Proof.Bignum.Arm.LoadBEFn
import VerifiedGarbage.Proof.Bignum.Arm.LoadBEFnArgs
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Bignum.Arm.MaskByteStep
import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.MaskOutput
import VerifiedGarbage.Proof.Bignum.Arm.MaskOutputArgs
import VerifiedGarbage.Proof.Bignum.Arm.Minv64
import VerifiedGarbage.Proof.Bignum.Arm.Minv64Steps
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckBounds
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckCalc
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckFinish
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckMath
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckRead
import VerifiedGarbage.Proof.Bignum.Arm.ModulusReady
import VerifiedGarbage.Proof.Bignum.Arm.MontBody
import VerifiedGarbage.Proof.Bignum.Arm.MontCore
import VerifiedGarbage.Proof.Bignum.Arm.MontFinish
import VerifiedGarbage.Proof.Bignum.Arm.MontFnBody
import VerifiedGarbage.Proof.Bignum.Arm.MontInitCT
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
import VerifiedGarbage.Proof.Bignum.Arm.MontOpArgs
import VerifiedGarbage.Proof.Bignum.Arm.MontRounds
import VerifiedGarbage.Proof.Bignum.Arm.MontRoundsCT
import VerifiedGarbage.Proof.Bignum.Arm.Mul64
import VerifiedGarbage.Proof.Bignum.Arm.Mul64Math
import VerifiedGarbage.Proof.Bignum.Arm.Newton64Math
import VerifiedGarbage.Proof.Bignum.Arm.Newton64Steps
import VerifiedGarbage.Proof.Bignum.Arm.PcBody
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
import VerifiedGarbage.Proof.Bignum.Arm.PcEntryMemory
import VerifiedGarbage.Proof.Bignum.Arm.PcEntryReady
import VerifiedGarbage.Proof.Bignum.Arm.PcFail
import VerifiedGarbage.Proof.Bignum.Arm.PcFailArgs
import VerifiedGarbage.Proof.Bignum.Arm.PcHead
import VerifiedGarbage.Proof.Bignum.Arm.PcValid
import VerifiedGarbage.Proof.Bignum.Arm.Precompute
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeInverse
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOut
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOutArgs
import VerifiedGarbage.Proof.Bignum.Arm.PrepareZero
import VerifiedGarbage.Proof.Bignum.Arm.ProductArgs
import VerifiedGarbage.Proof.Bignum.Arm.ProductStage
import VerifiedGarbage.Proof.Bignum.Arm.QuotientStage
import VerifiedGarbage.Proof.Bignum.Arm.R2
import VerifiedGarbage.Proof.Bignum.Arm.R2Constants
import VerifiedGarbage.Proof.Bignum.Arm.R2CountInit
import VerifiedGarbage.Proof.Bignum.Arm.R2Init
import VerifiedGarbage.Proof.Bignum.Arm.ReduceChoice
import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
import VerifiedGarbage.Proof.Bignum.Arm.ReductionStage
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.RestoreSlots
import VerifiedGarbage.Proof.Bignum.Arm.ReverseByteStep
import VerifiedGarbage.Proof.Bignum.Arm.ReverseEncoding
import VerifiedGarbage.Proof.Bignum.Arm.ReverseRegion
import VerifiedGarbage.Proof.Bignum.Arm.Round
import VerifiedGarbage.Proof.Bignum.Arm.RoundFinish
import VerifiedGarbage.Proof.Bignum.Arm.RoundFinishMemory
import VerifiedGarbage.Proof.Bignum.Arm.RoundFinishSteps
import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
import VerifiedGarbage.Proof.Bignum.Arm.Row
import VerifiedGarbage.Proof.Bignum.Arm.RowAdvance
import VerifiedGarbage.Proof.Bignum.Arm.RowBody
import VerifiedGarbage.Proof.Bignum.Arm.RowBody2
import VerifiedGarbage.Proof.Bignum.Arm.RowCarry
import VerifiedGarbage.Proof.Bignum.Arm.RowCarryMemory
import VerifiedGarbage.Proof.Bignum.Arm.RowFull
import VerifiedGarbage.Proof.Bignum.Arm.RowFullCT
import VerifiedGarbage.Proof.Bignum.Arm.RowStep
import VerifiedGarbage.Proof.Bignum.Arm.SanitizeBit
import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulus
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandArgs
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandLayout
import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasBody
import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasRow
import VerifiedGarbage.Proof.Bignum.Arm.SelectArray
import VerifiedGarbage.Proof.Bignum.Arm.SelectArrayArgs
import VerifiedGarbage.Proof.Bignum.Arm.SelectBody
import VerifiedGarbage.Proof.Bignum.Arm.SelectCT
import VerifiedGarbage.Proof.Bignum.Arm.SelectPrepare
import VerifiedGarbage.Proof.Bignum.Arm.SelectRow
import VerifiedGarbage.Proof.Bignum.Arm.SelectStep
import VerifiedGarbage.Proof.Bignum.Arm.SelectWord
import VerifiedGarbage.Proof.Bignum.Arm.SetBaseStep
import VerifiedGarbage.Proof.Bignum.Arm.SetBases
import VerifiedGarbage.Proof.Bignum.Arm.SetSmall
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallArgs
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallCT
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFnCT
import VerifiedGarbage.Proof.Bignum.Arm.Setup
import VerifiedGarbage.Proof.Bignum.Arm.SetupArgs
import VerifiedGarbage.Proof.Bignum.Arm.SetupFrame
import VerifiedGarbage.Proof.Bignum.Arm.Shift
import VerifiedGarbage.Proof.Bignum.Arm.ShiftArgs
import VerifiedGarbage.Proof.Bignum.Arm.ShiftCT
import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeft
import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeftStep
import VerifiedGarbage.Proof.Bignum.Arm.ShiftStep
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstLayout
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstLayoutCT
import VerifiedGarbage.Proof.Bignum.Arm.SquareBody
import VerifiedGarbage.Proof.Bignum.Arm.SquareCross
import VerifiedGarbage.Proof.Bignum.Arm.SquareFinish
import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.StackPair
import VerifiedGarbage.Proof.Bignum.Arm.Store64
import VerifiedGarbage.Proof.Bignum.Arm.Sub
import VerifiedGarbage.Proof.Bignum.Arm.Sub64
import VerifiedGarbage.Proof.Bignum.Arm.Sub64Math
import VerifiedGarbage.Proof.Bignum.Arm.SubAdvance
import VerifiedGarbage.Proof.Bignum.Arm.SubBody
import VerifiedGarbage.Proof.Bignum.Arm.SubRow
import VerifiedGarbage.Proof.Bignum.Arm.SubStep
import VerifiedGarbage.Proof.Bignum.Arm.WideMath
import VerifiedGarbage.Proof.Bignum.Arm.WideValue
import VerifiedGarbage.Proof.Bignum.Arm.ZeroStep
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.TaintErase
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.MdStream.Arm.Words
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.Rc2.Memory32
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Rsa.AcceptanceMask32
import VerifiedGarbage.Proof.Rsa.Arm.PrivAllocCT
import VerifiedGarbage.Proof.Rsa.Arm.PrivArgsCT
import VerifiedGarbage.Proof.Rsa.Arm.PrivBody
import VerifiedGarbage.Proof.Rsa.Arm.PrivBodyCT
import VerifiedGarbage.Proof.Rsa.Arm.PrivCallPublic
import VerifiedGarbage.Proof.Rsa.Arm.PrivCallsCT
import VerifiedGarbage.Proof.Rsa.Arm.PrivCheck
import VerifiedGarbage.Proof.Rsa.Arm.PrivCheckFrame
import VerifiedGarbage.Proof.Rsa.Arm.PrivCheckLogic
import VerifiedGarbage.Proof.Rsa.Arm.PrivCopyArgs
import VerifiedGarbage.Proof.Rsa.Arm.PrivCopyIncoming
import VerifiedGarbage.Proof.Rsa.Arm.PrivCopyRetained
import VerifiedGarbage.Proof.Rsa.Arm.PrivCrtCall
import VerifiedGarbage.Proof.Rsa.Arm.PrivMask
import VerifiedGarbage.Proof.Rsa.Arm.PrivPdCall
import VerifiedGarbage.Proof.Rsa.Arm.PrivPdSuffix
import VerifiedGarbage.Proof.Rsa.Arm.PrivPreWords
import VerifiedGarbage.Proof.Rsa.Arm.PrivRegions
import VerifiedGarbage.Proof.Rsa.Arm.PrivRelease
import VerifiedGarbage.Proof.Rsa.Arm.PrivReleaseArgs
import VerifiedGarbage.Proof.Rsa.Arm.PrivReleaseBuffer
import VerifiedGarbage.Proof.Rsa.Arm.PrivReleaseCT
import VerifiedGarbage.Proof.Rsa.Arm.PrivReleaseStep
import VerifiedGarbage.Proof.Rsa.Arm.PrivSaveIncoming
import VerifiedGarbage.Proof.Rsa.Arm.PrivSaveRegs
import VerifiedGarbage.Proof.Rsa.Arm.PrivSaveResult
import VerifiedGarbage.Proof.Rsa.Arm.PrivStackWord
import VerifiedGarbage.Proof.Rsa.Arm.PrivStatusPreserved
import VerifiedGarbage.Proof.Rsa.Arm.PrivStoreTemporary
import VerifiedGarbage.Proof.Rsa.Arm.PrivTailCT
import VerifiedGarbage.Proof.Rsa.Arm.PrivTailContext
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Rsa.ZeroTest32
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Spec.Pbkdf2.Generic

/-!
# RSASSA-PSS on ARMv7: hashing a message of secret length

`ctHash_vp`: from a state whose `Y` holds the message `msg σ` followed by
zeros up to `nbm` blocks, with its length and `nbm` in their slots, `ctHash`
leaves the digest of the message at `oDig`, keeping any fact about memory
that its writes (`ctW`) do not reach.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.MdStream (Md)

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- What `ctHash` writes. -/
abbrev ctW (L : Lay) (scr : BitVec 32) (T : Nat) : List Region :=
  [sR scr oSt (h.N + h.B), L.LOW, sR scr oLen h.B, sR scr oY T, sR scr oSt h.N, sR scr oCW h.H.md.so,
    sR scr oSel h.N, slotR L sBi, sR scr oDig h.N]

/-- The digest of the hash value at `oSel`, to `oDig`. -/
theorem out_vp (hg : Geo L scr) {X : State → Mem → Prop} :
    VP (fun σ s => Ctx L scr σ s ∧ X σ s.mem) (outPart h.H)
      (fun σ s => Ctx L scr σ s ∧ ∃ m₀, X σ m₀ ∧ Frame [sR scr oDig h.N] m₀ s.mem ∧
        s.mem = VG.WriteBytes.writeBytes m₀ (sa scr oDig) (h.md.digest (h.md.stateAt m₀ (sa scr oSel)))) := by
  have hN := h.N_le
  have fit := hg.fit
  obtain ⟨σ', ok⟩ := hg.ok
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ s.gpr .r0 = scr + BitVec.ofNat 32 oSel ∧
      s.gpr .r6 = scr + BitVec.ofNat 32 oDig)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hx⟩ => ?_) ?_
  · have hw : WP isa (.block outSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = scr + BitVec.ofNat 32 oSel ∧ t.gpr .r6 = scr + BitVec.ofNat 32 oDig := by
      prun [outSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS,
        movw_val (show oSel < 2 ^ 16 by decide), movw_val (show oDig < 2 ^ 16 by decide)]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r6⟩ => ⟨hc.regs rd wr sp m, m ▸ hx, r0, r6⟩
  refine VP.taint [.r0, .r6] h.outCk (fun _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]) fun σ s ⟨hc, hx, r0, r6⟩ => ?_
  have a0 : State.addr (s.gpr .r0) = sa scr oSel := by rw [r0]; exact hg.addr (by decide)
  have a6 : State.addr (s.gpr .r6) = sa scr oDig := by rw [r6]; exact hg.addr (by decide)
  refine WP.mono (h.ok.out s (by rw [r0, hg.scr_lt (by decide)]; pomega) (by rw [r6, hg.scr_lt (by decide)]; pomega)
    (by rw [a0]; exact hg.rd hc.st (by pomega)) (by rw [a6]; exact hg.wr hc.st (by pomega))
    (by rw [a0, a6]; exact Geo.sep (by pomega) (by pomega) (by pomega))) fun t ⟨_, rd, wr, sp, m⟩ => ?_
  rw [a0, a6] at m
  have hl := h.md.digest_length (h.md.stateAt s.mem (sa scr oSel))
  have fr : Frame [sR scr oDig h.N] s.mem t.mem := by
    rw [m]
    intro a ha
    simp only [List.mem_singleton, forall_eq, Region.Contains, VG.WriteBytes.writeBytes, hl] at ha ⊢
    rw [ite_eq_right (by omega)]
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, s.mem, hx, fr, m⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by pomega)
  · simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by pomega) (by rw [hg.F]; decide)

/-- A byte of our part of `scratch` after bytes are written there. -/
theorem sa_writeBytes (scr : BitVec 32) (m : Mem) {o i : Nat} {xs : List Byte} (hi : i < xs.length)
    (ho : o + i < 2 ^ 64) : VG.WriteBytes.writeBytes m (sa scr o) xs (sa scr (o + i)) = xs.getD i 0 := by
  simp only [VG.WriteBytes.writeBytes, sa, Offset.sub_toNat _ (Nat.le_add_right o i) ho, Nat.add_sub_cancel_left,
    hi, ↓reduceIte]

/-- `ctHash`: the digest of the message in `Y`, of a length in its slot,
padded in `nbm` blocks. -/
theorem ctHash_vp (hg : Geo L scr) {nbm : Nat} (hnb : nbm * h.B ≤ 2048) (hnb0 : 0 < nbm)
    {msg : State → List Byte} (hfit : ∀ σ, (msg σ).length + 1 + h.L ≤ nbm * h.B) {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame (ctW h L scr (nbm * h.B)) m m' → Inv σ m')
    (hsl : ∀ σ m, Inv σ m → m.readW (L.fr sL) 32 = BitVec.ofNat 32 (msg σ).length)
    (hsn : ∀ σ m, Inv σ m → m.readW (L.fr sNb) 32 = BitVec.ofNat 32 nbm) :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ ∀ i < nbm * h.B, s.mem (sa scr (oY + i)) = (msg σ).getD i 0)
      (ctHash h.H)
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧
        ∀ i < h.D, s.mem (sa scr (oDig + i)) = (h.ok.SH.H.hash (msg σ)).getD i 0) := by
  have hN := h.N_le
  have hB := h.B_le
  have hB64 := h.B_ge
  have hL := h.L_le
  have hNL := h.NL
  have hDN := h.D_le
  have fit := hg.fit
  have hB0 : 0 < h.B := by omega
  have hLB : h.L < h.B := by have := h.D_pos; omega
  obtain ⟨σ', ok⟩ := hg.ok
  have hIs : ∀ rs : List Region, (∀ r ∈ rs, r ∈ ctW h L scr (nbm * h.B)) →
      ∀ σ m m', Inv σ m → Frame rs m m' → Inv σ m' :=
    fun rs hs σ m m' hi hf => hI σ m m' hi (Frame.subset hf hs)
  have hq : ∀ σ, ((msg σ).length + h.L) / h.B < nbm := fun σ =>
    (Nat.div_lt_iff_lt_mul hB0).2 (by have := hfit σ; omega)
  have hℓ : ∀ σ, (msg σ).length < 2048 := fun σ => by have := hfit σ; omega
  show VP _ (.seq (initPart h.H) (.seq (lenPart h.H) (.seq (padPart h.H) (.seq (compLoop h.H) (outPart h.H))))) _
  -- the hash value initialized
  refine VP.seq (init_vp h hg (Inv := fun σ m => Inv σ m ∧ ∀ i < nbm * h.B, m (sa scr (oY + i)) = (msg σ).getD i 0)
    fun σ m m' ⟨hi, hy⟩ hf => ⟨hIs _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp) σ m m' hi hf,
      sbytes_keep hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Geo.sep (by pomega) (by pomega) (by pomega)
        · exact hg.low ok (by pomega)) (by pomega) hy⟩) ?_
  -- the length field
  refine VP.seq (((lenBlk_vp h hg (ℓ := fun σ => (msg σ).length) (Inv := fun σ m =>
      (Inv σ m ∧ ∀ i < nbm * h.B, m (sa scr (oY + i)) = (msg σ).getD i 0) ∧
        h.md.stateAt m (sa scr oSt) = h.ok.iv)
    (fun σ m m' ⟨⟨hi, hy⟩, he⟩ hf => ⟨⟨hIs _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; simp) σ m m' hi hf,
      sbytes_keep hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Geo.sep (by pomega) (by pomega) (by pomega)) (by pomega) hy⟩,
      (stateAt_keep h hf fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Geo.sep (by pomega) (by pomega) (by pomega)).trans he⟩)
    fun σ => by have := hℓ σ; omega)).mono
      (fun σ s ⟨hc, hi, he⟩ => ⟨hc, ⟨hi, he⟩, hsl σ _ hi.1⟩) fun _ _ h => h) ?_
  -- the padding
  refine VP.seq ((pad_vp h hg hnb hnb0 hfit (Inv := fun σ m => Inv σ m ∧ h.md.stateAt m (sa scr oSt) = h.ok.iv)
    (fun σ m m' ⟨hi, he⟩ hf => ⟨hIs _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; simp) σ m m' hi hf,
      (stateAt_keep h hf fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Geo.sep (by pomega) (by pomega) (by pomega)).trans he⟩)
    (fun σ m hi => hsl σ m hi.1) (fun σ m hi => hsn σ m hi.1)).mono
      (fun σ s ⟨hc, ⟨⟨hi, hy⟩, he⟩, hlb⟩ => ⟨hc, ⟨hi, he⟩, hlb, hy⟩) fun _ _ h => h) ?_
  -- every block compressed
  refine VP.seq ((compLoop_vp h hg hnb hnb0 (ℓ := fun σ => (msg σ).length)
    (yv := fun σ i => padY h.B h.L (msg σ) (h.md.lenBytes (msg σ).length) i) hq hℓ (Inv := Inv)
    (hIs _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> simp))
    (fun σ m hi => hsl σ m hi) (fun σ m hi => hsn σ m hi)).mono
      (fun σ s ⟨hc, ⟨hi, he⟩, hy⟩ => ⟨hc, hi, hy, he⟩) fun _ _ h => h) ?_
  -- the digest
  refine (out_vp h hg (X := fun σ m => Inv σ m ∧ h.md.stateAt m (sa scr oSel) =
      h.md.compressList h.ok.iv (ylist (fun i => padY h.B h.L (msg σ) (h.md.lenBytes (msg σ).length) i) (nbm * h.B))
        (((msg σ).length + h.L) / h.B + 1))).mono (fun _ _ h => h) fun σ s ⟨hc, m₀, ⟨hi, he⟩, hf, hm⟩ => ?_
  refine ⟨hc, hIs _ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; simp) σ _ _ hi hf, fun i hi => ?_⟩
  have hl := h.md.digest_length (h.md.stateAt m₀ (sa scr oSel))
  rw [hm, sa_writeBytes scr m₀ (by omega) (by pomega), he, h.ok.hash]
  have hq1 : ((msg σ).length + h.L) / h.B + 1 ≤ nbm := hq σ
  have key : h.md.compressList h.ok.iv
      (ylist (fun i => padY h.B h.L (msg σ) (h.md.lenBytes (msg σ).length) i) (nbm * h.B))
        (((msg σ).length + h.L) / h.B + 1) =
      h.md.compressList h.ok.iv (h.md.pad (msg σ)) ((h.md.pad (msg σ)).length / h.B) := by
    rw [RsaPss.pad_length h.md _ hB0 hLB, Nat.mul_div_cancel_left _ hB0]
    refine h.md.compressList_congr fun j hj => ?_
    have hT : j < nbm * h.B := by
      have := Nat.mul_le_mul_left h.B hq1
      rw [Nat.mul_comm h.B nbm] at this
      omega
    rw [ylist_getD hT, padY_eq hB0 hLB _ _ hj, RsaPss.pad_getD h.md _ hB0 hLB hj]
  rw [key, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
  rfl

end VG.Proof.RsaPss.Arm
