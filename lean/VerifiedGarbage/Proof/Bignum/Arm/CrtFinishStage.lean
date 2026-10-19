module
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedState
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState

public import VerifiedGarbage.Proof.Bignum.Arm.CrtRecombineStage
public import VerifiedGarbage.Proof.Bignum.Arm.CrtExportGeometry
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.ActivateWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.ArgsCT
import VerifiedGarbage.Proof.Bignum.Arm.ArrayFrame
import VerifiedGarbage.Proof.Bignum.Arm.BasesTail
import VerifiedGarbage.Proof.Bignum.Arm.ByteWords
import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWide
import VerifiedGarbage.Proof.Bignum.Arm.ClearOperandBuffer
import VerifiedGarbage.Proof.Bignum.Arm.ClearOperandBufferArgs
import VerifiedGarbage.Proof.Bignum.Arm.ControlBuffers
import VerifiedGarbage.Proof.Bignum.Arm.CopyBuffer
import VerifiedGarbage.Proof.Bignum.Arm.CopyByteStep
import VerifiedGarbage.Proof.Bignum.Arm.CopyRegion
import VerifiedGarbage.Proof.Bignum.Arm.CrtAddWideArgs
import VerifiedGarbage.Proof.Bignum.Arm.CrtAddWideScalars
import VerifiedGarbage.Proof.Bignum.Arm.CrtAdvanceLink
import VerifiedGarbage.Proof.Bignum.Arm.CrtCheckProduct
import VerifiedGarbage.Proof.Bignum.Arm.CrtClearWide
import VerifiedGarbage.Proof.Bignum.Arm.CrtClearWideArgs
import VerifiedGarbage.Proof.Bignum.Arm.CrtCompareArgs
import VerifiedGarbage.Proof.Bignum.Arm.CrtCopyChildPointer
import VerifiedGarbage.Proof.Bignum.Arm.CrtCopyHeaderPointer
import VerifiedGarbage.Proof.Bignum.Arm.CrtEnterPrime
import VerifiedGarbage.Proof.Bignum.Arm.CrtFactorProduct
import VerifiedGarbage.Proof.Bignum.Arm.CrtImportFinalResidue
import VerifiedGarbage.Proof.Bignum.Arm.CrtInitialize
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Bignum.Arm.CrtLeavePrime
import VerifiedGarbage.Proof.Bignum.Arm.CrtLinkStep
import VerifiedGarbage.Proof.Bignum.Arm.CrtLinks
import VerifiedGarbage.Proof.Bignum.Arm.CrtPadAfterProduct
import VerifiedGarbage.Proof.Bignum.Arm.CrtPadModulus
import VerifiedGarbage.Proof.Bignum.Arm.CrtPadModulusArgs
import VerifiedGarbage.Proof.Bignum.Arm.CrtPrepare
import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimeArgs
import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimeEnter
import VerifiedGarbage.Proof.Bignum.Arm.CrtProductArgs
import VerifiedGarbage.Proof.Bignum.Arm.CrtProductCount
import VerifiedGarbage.Proof.Bignum.Arm.CrtProductStart
import VerifiedGarbage.Proof.Bignum.Arm.CrtProductValidationState
import VerifiedGarbage.Proof.Bignum.Arm.CrtProductValues
import VerifiedGarbage.Proof.Bignum.Arm.CrtQSource
import VerifiedGarbage.Proof.Bignum.Arm.CrtRecombine
import VerifiedGarbage.Proof.Bignum.Arm.CrtRecombineGeometry
import VerifiedGarbage.Proof.Bignum.Arm.CrtRecombineValue
import VerifiedGarbage.Proof.Bignum.Arm.CrtSaveMain
import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupAll
import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupFrame
import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupMain
import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupPrime
import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Bignum.Arm.CrtStrides
import VerifiedGarbage.Proof.Bignum.Arm.CrtValidationGeometry
import VerifiedGarbage.Proof.Bignum.Arm.CrtValidationPreserved
import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceCall
import VerifiedGarbage.Proof.Bignum.Arm.CsubCT
import VerifiedGarbage.Proof.Bignum.Arm.CsubValue
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopSteps
import VerifiedGarbage.Proof.Bignum.Arm.EqualBuffers
import VerifiedGarbage.Proof.Bignum.Arm.EqualControls
import VerifiedGarbage.Proof.Bignum.Arm.EqualReverse
import VerifiedGarbage.Proof.Bignum.Arm.ExportArray
import VerifiedGarbage.Proof.Bignum.Arm.ExportArrayArgs
import VerifiedGarbage.Proof.Bignum.Arm.ExportBEArgs
import VerifiedGarbage.Proof.Bignum.Arm.ExportPadded
import VerifiedGarbage.Proof.Bignum.Arm.FinishArgs
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.HeaderDecrement
import VerifiedGarbage.Proof.Bignum.Arm.HeaderIncrement
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperandLayout
import VerifiedGarbage.Proof.Bignum.Arm.InitMetaMemory
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
import VerifiedGarbage.Proof.Bignum.Arm.MaskOutput
import VerifiedGarbage.Proof.Bignum.Arm.MaskOutputArgs
import VerifiedGarbage.Proof.Bignum.Arm.MontBody
import VerifiedGarbage.Proof.Bignum.Arm.MontCore
import VerifiedGarbage.Proof.Bignum.Arm.MontFinish
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
import VerifiedGarbage.Proof.Bignum.Arm.MontRounds
import VerifiedGarbage.Proof.Bignum.Arm.MontRoundsCT
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Bignum.Arm.PcHead
import VerifiedGarbage.Proof.Bignum.Arm.PcStack
import VerifiedGarbage.Proof.Bignum.Arm.PrepareZero
import VerifiedGarbage.Proof.Bignum.Arm.ProductArgs
import VerifiedGarbage.Proof.Bignum.Arm.ProductRowMath
import VerifiedGarbage.Proof.Bignum.Arm.ProductStage
import VerifiedGarbage.Proof.Bignum.Arm.ProductWindow
import VerifiedGarbage.Proof.Bignum.Arm.QuotientStage
import VerifiedGarbage.Proof.Bignum.Arm.ReadPrefix
import VerifiedGarbage.Proof.Bignum.Arm.ReduceChoice
import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
import VerifiedGarbage.Proof.Bignum.Arm.ReductionStage
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.ReverseBuffer
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
import VerifiedGarbage.Proof.Bignum.Arm.ShiftStep
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstLayout
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstLayoutCT
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.StackPair
import VerifiedGarbage.Proof.Bignum.Arm.Store64
import VerifiedGarbage.Proof.Bignum.Arm.StoreBE
import VerifiedGarbage.Proof.Bignum.Arm.Sub
import VerifiedGarbage.Proof.Bignum.Arm.SubAdvance
import VerifiedGarbage.Proof.Bignum.Arm.SubBody
import VerifiedGarbage.Proof.Bignum.Arm.SubCompare
import VerifiedGarbage.Proof.Bignum.Arm.SubCompareRow
import VerifiedGarbage.Proof.Bignum.Arm.SubRow
import VerifiedGarbage.Proof.Bignum.Arm.SubStep
import VerifiedGarbage.Proof.Bignum.Arm.TransferArray
import VerifiedGarbage.Proof.Bignum.Arm.TransferArrayArgs
import VerifiedGarbage.Proof.Bignum.Arm.WideMath
import VerifiedGarbage.Proof.Bignum.Arm.WideProduct
import VerifiedGarbage.Proof.Bignum.Arm.WideProductArgs
import VerifiedGarbage.Proof.Bignum.Arm.WideProductBody
import VerifiedGarbage.Proof.Bignum.Arm.WideProductMemory
import VerifiedGarbage.Proof.Bignum.Arm.WideProductNext
import VerifiedGarbage.Proof.Bignum.Arm.WideProductRow
import VerifiedGarbage.Proof.Bignum.Arm.WideValue
import VerifiedGarbage.Proof.Bignum.Arm.ZeroStep
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.ReadPrefix
import VerifiedGarbage.Proof.Bignum.ReverseEncoding
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.TaintErase
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Bignum.Arm.ActivateWorkspace
public import VerifiedGarbage.Proof.Bignum.Arm.ArgsCT
public import VerifiedGarbage.Proof.Bignum.Arm.ArrayFrame
public import VerifiedGarbage.Proof.Bignum.Arm.BasesTail
public import VerifiedGarbage.Proof.Bignum.Arm.ByteWords
public import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWide
public import VerifiedGarbage.Proof.Bignum.Arm.ClearOperandBuffer
public import VerifiedGarbage.Proof.Bignum.Arm.ClearOperandBufferArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ControlBuffers
public import VerifiedGarbage.Proof.Bignum.Arm.CopyBuffer
public import VerifiedGarbage.Proof.Bignum.Arm.CopyByteStep
public import VerifiedGarbage.Proof.Bignum.Arm.CopyRegion
public import VerifiedGarbage.Proof.Bignum.Arm.CrtAddWideArgs
public import VerifiedGarbage.Proof.Bignum.Arm.CrtAddWideScalars
public import VerifiedGarbage.Proof.Bignum.Arm.CrtAdvanceLink
public import VerifiedGarbage.Proof.Bignum.Arm.CrtCheckProduct
public import VerifiedGarbage.Proof.Bignum.Arm.CrtClearWide
public import VerifiedGarbage.Proof.Bignum.Arm.CrtClearWideArgs
public import VerifiedGarbage.Proof.Bignum.Arm.CrtCompareArgs
public import VerifiedGarbage.Proof.Bignum.Arm.CrtCopyChildPointer
public import VerifiedGarbage.Proof.Bignum.Arm.CrtCopyHeaderPointer
public import VerifiedGarbage.Proof.Bignum.Arm.CrtEnterPrime
public import VerifiedGarbage.Proof.Bignum.Arm.CrtFactorProduct
public import VerifiedGarbage.Proof.Bignum.Arm.CrtImportFinalResidue
public import VerifiedGarbage.Proof.Bignum.Arm.CrtInitialize
public import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
public import VerifiedGarbage.Proof.Bignum.Arm.CrtLeavePrime
public import VerifiedGarbage.Proof.Bignum.Arm.CrtLinkStep
public import VerifiedGarbage.Proof.Bignum.Arm.CrtLinks
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPadAfterProduct
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPadModulus
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPadModulusArgs
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPrepare
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimeArgs
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimeEnter
public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductArgs
public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductCount
public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductStart
public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductValidationState
public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductValues
public import VerifiedGarbage.Proof.Bignum.Arm.CrtQSource
public import VerifiedGarbage.Proof.Bignum.Arm.CrtRecombine
public import VerifiedGarbage.Proof.Bignum.Arm.CrtRecombineGeometry
public import VerifiedGarbage.Proof.Bignum.Arm.CrtRecombineValue
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSaveMain
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupAll
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupFrame
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupMain
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupPrime
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedWorkspace
public import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
public import VerifiedGarbage.Proof.Bignum.Arm.CrtStrides
public import VerifiedGarbage.Proof.Bignum.Arm.CrtValidationGeometry
public import VerifiedGarbage.Proof.Bignum.Arm.CrtValidationPreserved
public import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceCall
public import VerifiedGarbage.Proof.Bignum.Arm.CsubCT
public import VerifiedGarbage.Proof.Bignum.Arm.CsubValue
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopSteps
public import VerifiedGarbage.Proof.Bignum.Arm.EqualBuffers
public import VerifiedGarbage.Proof.Bignum.Arm.EqualControls
public import VerifiedGarbage.Proof.Bignum.Arm.EqualReverse
public import VerifiedGarbage.Proof.Bignum.Arm.ExportArray
public import VerifiedGarbage.Proof.Bignum.Arm.ExportArrayArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ExportBEArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ExportPadded
public import VerifiedGarbage.Proof.Bignum.Arm.FinishArgs
public import VerifiedGarbage.Proof.Bignum.Arm.HeaderDecrement
public import VerifiedGarbage.Proof.Bignum.Arm.HeaderIncrement
public import VerifiedGarbage.Proof.Bignum.Arm.ImportOperandLayout
public import VerifiedGarbage.Proof.Bignum.Arm.InitMetaMemory
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
public import VerifiedGarbage.Proof.Bignum.Arm.MaskOutput
public import VerifiedGarbage.Proof.Bignum.Arm.MaskOutputArgs
public import VerifiedGarbage.Proof.Bignum.Arm.MontBody
public import VerifiedGarbage.Proof.Bignum.Arm.MontCore
public import VerifiedGarbage.Proof.Bignum.Arm.MontFinish
public import VerifiedGarbage.Proof.Bignum.Arm.MontMath
public import VerifiedGarbage.Proof.Bignum.Arm.MontRounds
public import VerifiedGarbage.Proof.Bignum.Arm.MontRoundsCT
public import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
public import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
public import VerifiedGarbage.Proof.Bignum.Arm.PcHead
public import VerifiedGarbage.Proof.Bignum.Arm.PcStack
public import VerifiedGarbage.Proof.Bignum.Arm.PrepareZero
public import VerifiedGarbage.Proof.Bignum.Arm.ProductArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ProductRowMath
public import VerifiedGarbage.Proof.Bignum.Arm.ProductStage
public import VerifiedGarbage.Proof.Bignum.Arm.ProductWindow
public import VerifiedGarbage.Proof.Bignum.Arm.QuotientStage
public import VerifiedGarbage.Proof.Bignum.Arm.ReadPrefix
public import VerifiedGarbage.Proof.Bignum.Arm.ReduceChoice
public import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ReductionStage
public import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
public import VerifiedGarbage.Proof.Bignum.Arm.ReverseBuffer
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
public import VerifiedGarbage.Proof.Bignum.Arm.ShiftStep
public import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
public import VerifiedGarbage.Proof.Bignum.Arm.SmallConstLayout
public import VerifiedGarbage.Proof.Bignum.Arm.SmallConstLayoutCT
public import VerifiedGarbage.Proof.Bignum.Arm.Stack
public import VerifiedGarbage.Proof.Bignum.Arm.StackCT
public import VerifiedGarbage.Proof.Bignum.Arm.StackPair
public import VerifiedGarbage.Proof.Bignum.Arm.Store64
public import VerifiedGarbage.Proof.Bignum.Arm.StoreBE
public import VerifiedGarbage.Proof.Bignum.Arm.Sub
public import VerifiedGarbage.Proof.Bignum.Arm.SubAdvance
public import VerifiedGarbage.Proof.Bignum.Arm.SubBody
public import VerifiedGarbage.Proof.Bignum.Arm.SubCompare
public import VerifiedGarbage.Proof.Bignum.Arm.SubCompareRow
public import VerifiedGarbage.Proof.Bignum.Arm.SubRow
public import VerifiedGarbage.Proof.Bignum.Arm.SubStep
public import VerifiedGarbage.Proof.Bignum.Arm.TransferArray
public import VerifiedGarbage.Proof.Bignum.Arm.TransferArrayArgs
public import VerifiedGarbage.Proof.Bignum.Arm.WideMath
public import VerifiedGarbage.Proof.Bignum.Arm.WideProduct
public import VerifiedGarbage.Proof.Bignum.Arm.WideProductArgs
public import VerifiedGarbage.Proof.Bignum.Arm.WideProductBody
public import VerifiedGarbage.Proof.Bignum.Arm.WideProductMemory
public import VerifiedGarbage.Proof.Bignum.Arm.WideProductNext
public import VerifiedGarbage.Proof.Bignum.Arm.WideProductRow
public import VerifiedGarbage.Proof.Bignum.Arm.WideValue
public import VerifiedGarbage.Proof.Bignum.Arm.ZeroStep
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Framework.Arm.TaintErase
public import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Rc2.Memory32
public import VerifiedGarbage.Proof.Rc2.PairMem
public import VerifiedGarbage.Proof.Rsa.AcceptanceMask32
import VerifiedGarbage.Proof.Rc2.Memory32
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Rsa.AcceptanceMask32
import VerifiedGarbage.Proof.Rsa.BytesFrame

/-! # Reconstruct and export exactly the accepted CRT result, or all zero bytes -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

def crtReconstruction (g : CrtGeometry) (m : Mem) : Nat :=
  numAt m (State.addr (crtP g.base g.words)) g.words 5 *
    numAt m (State.addr (crtQ g.base g.words)) g.words 0 +
    numAt m (State.addr (crtQ g.base g.words)) g.words 6

theorem crt_finishStage_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {accepted : Bool}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s)
    (flag : s.mem.readW (off (State.addr s.sp) 48) 32 = BitVec.ofNat 32 accepted.toNat)
    (bound : accepted = true → crtReconstruction g s.mem < 2 ^ (8 * g.length)) :
    WP isa CrtFn.finish s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr g.output) g.length =
        (if accepted then Spec.Rsa.i2osp (crtReconstruction g s.mem) g.length else List.replicate g.length 0) ∧
      t.gpr .r0 = BitVec.ofNat 32 accepted.toNat ∧
      Frame [⟨State.addr g.base, g.size⟩, ⟨State.addr g.output, g.length⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  unfold CrtFn.finish
  apply WP.assoc
  apply WP.assoc
  rw [WP.seq_iff]
  refine WP.mono (crt_recombineStage_ok s h ready) ?_
  rintro u ⟨sharedU, readyU, value, frameU, restU⟩
  have stackEq : WorkspaceEq (State.addr s.sp) 112 s.mem u.mem := WorkspaceEq.of_frame (by decide) frameU (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.stack.separate)
  have flagU : u.mem.readW (off (State.addr u.sp) 48) 32 = BitVec.ofNat 32 accepted.toNat := by
    rw [restU.sp, stackEq.word (d := 48) (bits := 32) (by decide)]; exact flag
  rw [WP.seq_iff]
  refine WP.mono (crt_outputArgs_ok u sharedU readyU.ptr) ?_
  rintro v ⟨source, output, count, memV, restV⟩
  have sharedV := sharedU.of_mem memV restV
  have input := sharedV.export_input source output count
    (by rw [memV, restV.sp]; exact flagU)
    (by rw [memV, value]; exact bound)
  refine WP.mono (exportBufferMasked_ok v input) ?_
  rintro t ⟨bytes, status, frameT, restT⟩
  rw [sharedV.product_read, memV, value] at bytes
  rw [memV] at frameT
  exact ⟨bytes, status, (frameU.mono (by simp)).trans (frameT.mono (by simp)),
    restU.trans ((restV.mono (by simp [roundClobbers])).trans restT)⟩

end VG.Proof.Bignum.Arm
