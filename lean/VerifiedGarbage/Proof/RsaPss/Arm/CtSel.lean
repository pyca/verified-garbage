module

public meta import VerifiedGarbage.Proof.RsaPss.Arm.CtPad
public import VerifiedGarbage.Proof.RsaPss.Arm.CtBase
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Impl.Aes.Arm.Alloc
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
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
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
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.ModulusCheckMath
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.ReverseEncoding
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.TaintErase
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.MdStream.Arm.Words
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Pbkdf2.Memory
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
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Rsa.ZeroTest32
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.RsaPss.Arm.CtInit
import VerifiedGarbage.Proof.RsaPss.Arm.CtPad
import VerifiedGarbage.Proof.Sha256.StateMem
import VerifiedGarbage.Spec.Pbkdf2.Generic
meta import VerifiedGarbage.Impl.Aes.Arm.Alloc
meta import VerifiedGarbage.Proof.AesGcm.Arm.Compare
meta import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.Arm.Entry
meta import VerifiedGarbage.Proof.AesGcm.Arm.Ghash1
meta import VerifiedGarbage.Proof.Bignum.Arm.ActivateWorkspace
meta import VerifiedGarbage.Proof.Bignum.Arm.AddCarry
meta import VerifiedGarbage.Proof.Bignum.Arm.ArgsCT
meta import VerifiedGarbage.Proof.Bignum.Arm.ArrayFrame
meta import VerifiedGarbage.Proof.Bignum.Arm.BasesTail
meta import VerifiedGarbage.Proof.Bignum.Arm.ByteWords
meta import VerifiedGarbage.Proof.Bignum.Arm.CompareBuffer
meta import VerifiedGarbage.Proof.Bignum.Arm.CompareByteStep
meta import VerifiedGarbage.Proof.Bignum.Arm.CompareBytes
meta import VerifiedGarbage.Proof.Bignum.Arm.CompareBytesCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CopyBuffer
meta import VerifiedGarbage.Proof.Bignum.Arm.CopyByteStep
meta import VerifiedGarbage.Proof.Bignum.Arm.CopyBytesCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CopyRegion
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtAdvanceLink
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtEnterPrime
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtInitialize
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtLeavePrime
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtLinkStep
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtLinks
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtPrepare
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimeArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimeEnter
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtSaveMain
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupAll
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupFrame
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupMain
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupPrime
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtStrides
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceCall
meta import VerifiedGarbage.Proof.Bignum.Arm.CsubCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CsubValue
meta import VerifiedGarbage.Proof.Bignum.Arm.DoubleBody
meta import VerifiedGarbage.Proof.Bignum.Arm.DoubleCore
meta import VerifiedGarbage.Proof.Bignum.Arm.DoubleCountMemory
meta import VerifiedGarbage.Proof.Bignum.Arm.DoubleFnBody
meta import VerifiedGarbage.Proof.Bignum.Arm.DoubleFnRestore
meta import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoop
meta import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopBody
meta import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopSteps
meta import VerifiedGarbage.Proof.Bignum.Arm.DoubleProduct
meta import VerifiedGarbage.Proof.Bignum.Arm.ExportArray
meta import VerifiedGarbage.Proof.Bignum.Arm.ExportArrayArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.ExportEncoding
meta import VerifiedGarbage.Proof.Bignum.Arm.FinishArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
meta import VerifiedGarbage.Proof.Bignum.Arm.ImportModulus
meta import VerifiedGarbage.Proof.Bignum.Arm.ImportOperandLayout
meta import VerifiedGarbage.Proof.Bignum.Arm.InitInverse
meta import VerifiedGarbage.Proof.Bignum.Arm.InitMetaMemory
meta import VerifiedGarbage.Proof.Bignum.Arm.InverseArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.InverseReady
meta import VerifiedGarbage.Proof.Bignum.Arm.KeepsBridge
meta import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
meta import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
meta import VerifiedGarbage.Proof.Bignum.Arm.LayoutExternal
meta import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
meta import VerifiedGarbage.Proof.Bignum.Arm.LoadArray
meta import VerifiedGarbage.Proof.Bignum.Arm.LoadBE
meta import VerifiedGarbage.Proof.Bignum.Arm.LoadBEArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.LoadBEFn
meta import VerifiedGarbage.Proof.Bignum.Arm.LoadBEFnArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
meta import VerifiedGarbage.Proof.Bignum.Arm.MaskByteStep
meta import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
meta import VerifiedGarbage.Proof.Bignum.Arm.MaskOutput
meta import VerifiedGarbage.Proof.Bignum.Arm.MaskOutputArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.Minv64
meta import VerifiedGarbage.Proof.Bignum.Arm.Minv64Steps
meta import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
meta import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckBounds
meta import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckCalc
meta import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckFinish
meta import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckMath
meta import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckRead
meta import VerifiedGarbage.Proof.Bignum.Arm.ModulusReady
meta import VerifiedGarbage.Proof.Bignum.Arm.MontBody
meta import VerifiedGarbage.Proof.Bignum.Arm.MontCore
meta import VerifiedGarbage.Proof.Bignum.Arm.MontFinish
meta import VerifiedGarbage.Proof.Bignum.Arm.MontFnBody
meta import VerifiedGarbage.Proof.Bignum.Arm.MontInitCT
meta import VerifiedGarbage.Proof.Bignum.Arm.MontMath
meta import VerifiedGarbage.Proof.Bignum.Arm.MontOpArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.MontRounds
meta import VerifiedGarbage.Proof.Bignum.Arm.MontRoundsCT
meta import VerifiedGarbage.Proof.Bignum.Arm.Mul64
meta import VerifiedGarbage.Proof.Bignum.Arm.Mul64Math
meta import VerifiedGarbage.Proof.Bignum.Arm.Newton64Math
meta import VerifiedGarbage.Proof.Bignum.Arm.Newton64Steps
meta import VerifiedGarbage.Proof.Bignum.Arm.PcBody
meta import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
meta import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
meta import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
meta import VerifiedGarbage.Proof.Bignum.Arm.PcEntryMemory
meta import VerifiedGarbage.Proof.Bignum.Arm.PcEntryReady
meta import VerifiedGarbage.Proof.Bignum.Arm.PcFail
meta import VerifiedGarbage.Proof.Bignum.Arm.PcFailArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.PcHead
meta import VerifiedGarbage.Proof.Bignum.Arm.PcValid
meta import VerifiedGarbage.Proof.Bignum.Arm.Precompute
meta import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeInverse
meta import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOut
meta import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOutArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.PrepareZero
meta import VerifiedGarbage.Proof.Bignum.Arm.ProductArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.ProductStage
meta import VerifiedGarbage.Proof.Bignum.Arm.QuotientStage
meta import VerifiedGarbage.Proof.Bignum.Arm.R2
meta import VerifiedGarbage.Proof.Bignum.Arm.R2Constants
meta import VerifiedGarbage.Proof.Bignum.Arm.R2CountInit
meta import VerifiedGarbage.Proof.Bignum.Arm.R2Init
meta import VerifiedGarbage.Proof.Bignum.Arm.ReduceChoice
meta import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.ReductionStage
meta import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
meta import VerifiedGarbage.Proof.Bignum.Arm.RestoreSlots
meta import VerifiedGarbage.Proof.Bignum.Arm.ReverseByteStep
meta import VerifiedGarbage.Proof.Bignum.Arm.ReverseEncoding
meta import VerifiedGarbage.Proof.Bignum.Arm.ReverseRegion
meta import VerifiedGarbage.Proof.Bignum.Arm.Round
meta import VerifiedGarbage.Proof.Bignum.Arm.RoundFinish
meta import VerifiedGarbage.Proof.Bignum.Arm.RoundFinishMemory
meta import VerifiedGarbage.Proof.Bignum.Arm.RoundFinishSteps
meta import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
meta import VerifiedGarbage.Proof.Bignum.Arm.Row
meta import VerifiedGarbage.Proof.Bignum.Arm.RowAdvance
meta import VerifiedGarbage.Proof.Bignum.Arm.RowBody
meta import VerifiedGarbage.Proof.Bignum.Arm.RowBody2
meta import VerifiedGarbage.Proof.Bignum.Arm.RowCarry
meta import VerifiedGarbage.Proof.Bignum.Arm.RowCarryMemory
meta import VerifiedGarbage.Proof.Bignum.Arm.RowFull
meta import VerifiedGarbage.Proof.Bignum.Arm.RowFullCT
meta import VerifiedGarbage.Proof.Bignum.Arm.RowStep
meta import VerifiedGarbage.Proof.Bignum.Arm.SanitizeBit
meta import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulus
meta import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandLayout
meta import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasBody
meta import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasRow
meta import VerifiedGarbage.Proof.Bignum.Arm.SelectArray
meta import VerifiedGarbage.Proof.Bignum.Arm.SelectArrayArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.SelectBody
meta import VerifiedGarbage.Proof.Bignum.Arm.SelectCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SelectPrepare
meta import VerifiedGarbage.Proof.Bignum.Arm.SelectRow
meta import VerifiedGarbage.Proof.Bignum.Arm.SelectStep
meta import VerifiedGarbage.Proof.Bignum.Arm.SelectWord
meta import VerifiedGarbage.Proof.Bignum.Arm.SetBaseStep
meta import VerifiedGarbage.Proof.Bignum.Arm.SetBases
meta import VerifiedGarbage.Proof.Bignum.Arm.SetSmall
meta import VerifiedGarbage.Proof.Bignum.Arm.SetSmallArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.SetSmallCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
meta import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFnCT
meta import VerifiedGarbage.Proof.Bignum.Arm.Setup
meta import VerifiedGarbage.Proof.Bignum.Arm.SetupArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.SetupFrame
meta import VerifiedGarbage.Proof.Bignum.Arm.Shift
meta import VerifiedGarbage.Proof.Bignum.Arm.ShiftArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.ShiftCT
meta import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeft
meta import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeftStep
meta import VerifiedGarbage.Proof.Bignum.Arm.ShiftStep
meta import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
meta import VerifiedGarbage.Proof.Bignum.Arm.SmallConstLayout
meta import VerifiedGarbage.Proof.Bignum.Arm.SmallConstLayoutCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SquareBody
meta import VerifiedGarbage.Proof.Bignum.Arm.SquareCross
meta import VerifiedGarbage.Proof.Bignum.Arm.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
meta import VerifiedGarbage.Proof.Bignum.Arm.Stack
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StackPair
meta import VerifiedGarbage.Proof.Bignum.Arm.Store64
meta import VerifiedGarbage.Proof.Bignum.Arm.Sub
meta import VerifiedGarbage.Proof.Bignum.Arm.Sub64
meta import VerifiedGarbage.Proof.Bignum.Arm.Sub64Math
meta import VerifiedGarbage.Proof.Bignum.Arm.SubAdvance
meta import VerifiedGarbage.Proof.Bignum.Arm.SubBody
meta import VerifiedGarbage.Proof.Bignum.Arm.SubRow
meta import VerifiedGarbage.Proof.Bignum.Arm.SubStep
meta import VerifiedGarbage.Proof.Bignum.Arm.WideMath
meta import VerifiedGarbage.Proof.Bignum.Arm.WideValue
meta import VerifiedGarbage.Proof.Bignum.Arm.ZeroStep
meta import VerifiedGarbage.Proof.Bignum.ByteWords
meta import VerifiedGarbage.Proof.Bignum.ExportEncoding
meta import VerifiedGarbage.Proof.Bignum.Layout
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.ModulusCheckMath
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.ReverseEncoding
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Bytes
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.TaintErase
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OffsetBelow
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Hmac.Common
meta import VerifiedGarbage.Proof.Hmac.Generic.Common
meta import VerifiedGarbage.Proof.MdStream.Arm.Words
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Pbkdf2.Memory
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
meta import VerifiedGarbage.Proof.Rc2.Memory32
meta import VerifiedGarbage.Proof.Rc2.PairMem
meta import VerifiedGarbage.Proof.Rsa.AcceptanceMask32
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivAllocCT
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivArgsCT
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivBody
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivBodyCT
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivCallPublic
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivCallsCT
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivCheck
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivCheckFrame
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivCheckLogic
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivCopyArgs
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivCopyIncoming
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivCopyRetained
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivCrtCall
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivMask
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivPdCall
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivPdSuffix
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivPreWords
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivRegions
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivRelease
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivReleaseArgs
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivReleaseBuffer
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivReleaseCT
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivReleaseStep
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivSaveIncoming
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivSaveRegs
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivSaveResult
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivStackWord
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivStatusPreserved
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivStoreTemporary
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivTailCT
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivTailContext
meta import VerifiedGarbage.Proof.Rsa.BytesFrame
meta import VerifiedGarbage.Proof.Rsa.Octets
meta import VerifiedGarbage.Proof.Rsa.ZeroTest32
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtInit
meta import VerifiedGarbage.Proof.Sha256.StateMem
meta import VerifiedGarbage.Spec.Pbkdf2.Generic

/-!
# RSASSA-PSS on ARMv7: hashing, the selection of the hash value

`sel_vp`: the selection loop copies the hash value at `oSt` to `oSel` under
a mask (all ones or zero, as a condition `c` on the run decides), and leaves
`oSel` as it was otherwise.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

/-- The mask of a condition. -/
def maskOf (c : Prop) [Decidable c] : BitVec 32 := if c then BitVec.allOnes 32 else 0

/-- The byte the selection stores. -/
theorem selByte (a b : Byte) (c : Prop) [Decidable c] :
    (b.setWidth 32 ^^^ ((a.setWidth 32 ^^^ b.setWidth 32) &&& maskOf c)).setWidth 8 = if c then a else b := by
  have e1 : ∀ x : BitVec 8, (x.setWidth 32).setWidth 8 = x := fun x => by simp
  by_cases hc : c <;> simp only [maskOf, hc, ite_true, ite_false, BitVec.and_allOnes, BitVec.setWidth_xor, e1]
  · rw [← BitVec.xor_assoc, BitVec.xor_comm b, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · simp

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- After `j` bytes of the selection, from memory `m₀`. -/
structure SI (scr : BitVec 32) (c : Prop) [Decidable c] (m₀ : Mem) (j : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = scr + BitVec.ofNat 32 (oSt + j)
  r1 : s.gpr .r1 = scr + BitVec.ofNat 32 (oSel + j)
  lr : s.gpr .lr = BitVec.ofNat 32 (h.N - j)
  r2 : s.gpr .r2 = maskOf c
  fr : Frame [sR scr oSel h.N] m₀ s.mem
  sel : ∀ i < h.N, s.mem (sa scr (oSel + i)) = if i < j ∧ c then m₀ (sa scr (oSt + i)) else m₀ (sa scr (oSel + i))

theorem selBody_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1, .lr])
    (.block selBody) hc).isSome = true := ⟨_, by taint_decide⟩

/-- The selection: the hash value at `oSt` copied to `oSel` if `c`. -/
theorem sel_vp (hg : Geo L scr) {c : State → Prop} [∀ σ, Decidable (c σ)] {X : State → Mem → Prop} :
    VP (fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ s.gpr .r0 = scr + BitVec.ofNat 32 oSt ∧
        s.gpr .r1 = scr + BitVec.ofNat 32 oSel ∧ s.gpr .lr = BitVec.ofNat 32 h.N ∧ s.gpr .r2 = maskOf (c σ))
      (countLoop selBody)
      (fun σ s => Ctx L scr σ s ∧ ∃ m₀, X σ m₀ ∧ Frame [sR scr oSel h.N] m₀ s.mem ∧
        ∀ i < h.N, s.mem (sa scr (oSel + i)) = if c σ then m₀ (sa scr (oSt + i)) else m₀ (sa scr (oSel + i))) := by
  have hN := h.N_le
  have hN0 : 0 < h.N := by have := h.D_pos; have := h.D_le; omega
  have fit := hg.fit
  obtain ⟨σ', ok⟩ := hg.ok
  let I : Nat → State → State → Prop := fun n σ s => n ≤ h.N ∧ Ctx L scr σ s ∧
    ∃ m₀, X σ m₀ ∧ SI h scr (c σ) m₀ (h.N - n) s
  refine (VP.loop (I := I) (fun n => ?_) (h.N - 1)).mono (fun σ s ⟨hc, hx, r0, r1, lr, r2⟩ => ⟨by omega, hc,
    s.mem, hx, ⟨by rw [r0, show h.N - (h.N - 1 + 1) = 0 by omega]; rfl, by rw [r1, show h.N - (h.N - 1 + 1) = 0 by omega]; rfl,
      by rw [lr, show h.N - (h.N - (h.N - 1 + 1)) = h.N by omega], r2, Frame.refl _ _, fun i _ => by
        rw [ite_eq_right (by omega)]⟩⟩) fun _ _ h => h
  refine VP.taint _ selBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hn, hc, m₀, hx, hp⟩ => ?_
  · obtain ⟨-, -, _, -, p₁⟩ := h₁
    obtain ⟨-, -, _, -, p₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [p₁.r0, p₂.r0]
    · rw [p₁.r1, p₂.r1]
    · rw [p₁.lr, p₂.lr]
  generalize hj : h.N - (n + 1) = j at hp
  have hjN : j < h.N := by omega
  have aS : State.addr (scr + BitVec.ofNat 32 (oSt + j)) = sa scr (oSt + j) := hg.addr (by pomega)
  have aE : State.addr (scr + BitVec.ofNat 32 (oSel + j)) = sa scr (oSel + j) := hg.addr (by pomega)
  have rS : InRegions (s.rd ++ s.wr) (sa scr (oSt + j)) 1 := hg.rd hc.st (by pomega)
  have rE : InRegions (s.rd ++ s.wr) (sa scr (oSel + j)) 1 := hg.rd hc.st (by pomega)
  have wE : InRegions s.wr (sa scr (oSel + j)) 1 := hg.wr hc.st (by pomega)
  have stj : s.mem (sa scr (oSt + j)) = m₀ (sa scr (oSt + j)) :=
    hp.fr _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Geo.sep (scr := scr) (o := oSt + j) (n := 1) (by pomega) (by pomega) (by pomega) _ (Region.contains_self _ _)
  have lr1 : BitVec.ofNat 32 (h.N - j) - 1 = BitVec.ofNat 32 (h.N - (j + 1)) := by
    rw [show h.N - j = (h.N - (j + 1)) + 1 by omega]; exact sub_one_ofNat (by omega)
  have hw : WP isa (.block selBody) s fun t => t.mem = s.mem.writeW (sa scr (oSel + j))
      (if c σ then m₀ (sa scr (oSt + j)) else s.mem (sa scr (oSel + j))) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ t.gpr .r0 = scr + BitVec.ofNat 32 (oSt + (j + 1)) ∧
      t.gpr .r1 = scr + BitVec.ofNat 32 (oSel + (j + 1)) ∧ t.gpr .lr = BitVec.ofNat 32 (h.N - (j + 1)) ∧
      t.gpr .r2 = s.gpr .r2 ∧ t.z = decide (h.N - (j + 1) = 0) := by
    prun [selBody, hp.r0, hp.r1, hp.r2, hp.lr, aS, aE, rS, rE, wE, stj, selByte, lr1, dpVal]
    refine ⟨?_, ?_, ?_⟩
    · rw [BitVec.add_assoc, VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32, Nat.add_assoc]
    · rw [BitVec.add_assoc, VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32, Nat.add_assoc]
    · rw [VG.Proof.X25519.Arm.ofNat_beq_zero (by omega)]
  refine WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr, r2, z⟩ => ?_
  have fr1 : Frame [sR scr oSel h.N] s.mem t.mem := by
    rw [m]; exact frame_byte scr _ _ (by omega) (by omega) (by pomega)
  have hc' : Ctx L scr σ t := hc.write fr1 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by pomega))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by pomega) (by rw [hg.F]; decide))
    rd wr sp
  have sk : SI h scr (c σ) m₀ (j + 1) t := by
    refine ⟨r0, r1, lr, r2.trans hp.r2, hp.fr.trans fr1, fun i hi => ?_⟩
    rw [m, sa_write scr _ _ (by pomega) (by pomega)]
    by_cases e : i = j
    · subst e
      rw [ite_eq_left rfl, hp.sel i hi, ite_eq_right (show ¬ (i < i ∧ c σ) from fun h => absurd h.1 (Nat.lt_irrefl _))]
      by_cases hc' : c σ
      · rw [ite_eq_left hc', ite_eq_left ⟨Nat.lt_succ_self _, hc'⟩]
      · rw [ite_eq_right hc', ite_eq_right (fun h => hc' h.2)]
    · rw [ite_eq_right (show ¬ (oSel + i = oSel + j) by omega), hp.sel i hi]
      by_cases e' : i < j
      · simp only [e', show i < j + 1 by omega, true_and]
      · simp only [e', show ¬ i < j + 1 by omega, false_and, ite_false]
  refine ⟨by rw [VG.Proof.X25519.Arm.eval_ne, z, show h.N - (j + 1) = n by omega]; cases n <;> simp,
    fun h0 => ⟨hc', m₀, hx, sk.fr, fun i hi => ?_⟩, fun hpos => ⟨by omega, hc', m₀, hx, ?_⟩⟩
  · rw [sk.sel i hi]
    by_cases hc'' : c σ
    · rw [ite_eq_left hc'', ite_eq_left ⟨by omega, hc''⟩]
    · rw [ite_eq_right hc'', ite_eq_right (fun h => hc'' h.2)]
  · rw [show h.N - n = j + 1 by omega]; exact sk

end VG.Proof.RsaPss.Arm
