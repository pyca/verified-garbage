module

public import VerifiedGarbage.Proof.RsaPss.Arm.VfScan
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
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
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticExternal
import VerifiedGarbage.Proof.Bignum.Arm.ArrayCompare
import VerifiedGarbage.Proof.Bignum.Arm.ArrayCompareArgs
import VerifiedGarbage.Proof.Bignum.Arm.ArrayCompareCT
import VerifiedGarbage.Proof.Bignum.Arm.ArrayFrame
import VerifiedGarbage.Proof.Bignum.Arm.BasesTail
import VerifiedGarbage.Proof.Bignum.Arm.ByteWords
import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWide
import VerifiedGarbage.Proof.Bignum.Arm.ClearOperandBuffer
import VerifiedGarbage.Proof.Bignum.Arm.ClearOperandBufferArgs
import VerifiedGarbage.Proof.Bignum.Arm.CompareBuffer
import VerifiedGarbage.Proof.Bignum.Arm.CompareByteStep
import VerifiedGarbage.Proof.Bignum.Arm.CompareBytes
import VerifiedGarbage.Proof.Bignum.Arm.CompareBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpBit
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpBitsCT
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpByte
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpByteHead
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpByteHeadCT
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpByteNext
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpByteSave
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpBytes
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpInit
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpPhase
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpPhaseCT
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpRound
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpRoundCT
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpStep
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpStepCT
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
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopCT
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopSteps
import VerifiedGarbage.Proof.Bignum.Arm.DoubleProduct
import VerifiedGarbage.Proof.Bignum.Arm.ExpBitTest
import VerifiedGarbage.Proof.Bignum.Arm.ExpByteLoad
import VerifiedGarbage.Proof.Bignum.Arm.ExpControl
import VerifiedGarbage.Proof.Bignum.Arm.ExpControls
import VerifiedGarbage.Proof.Bignum.Arm.ExpControlsCT
import VerifiedGarbage.Proof.Bignum.Arm.ExpInit
import VerifiedGarbage.Proof.Bignum.Arm.ExpInitCT
import VerifiedGarbage.Proof.Bignum.Arm.ExponentAccumulate
import VerifiedGarbage.Proof.Bignum.Arm.ExponentByte
import VerifiedGarbage.Proof.Bignum.Arm.ExponentCheck
import VerifiedGarbage.Proof.Bignum.Arm.ExponentCheckCT
import VerifiedGarbage.Proof.Bignum.Arm.ExponentCheckMath
import VerifiedGarbage.Proof.Bignum.Arm.ExponentFlag
import VerifiedGarbage.Proof.Bignum.Arm.ExponentSaturate
import VerifiedGarbage.Proof.Bignum.Arm.ExponentTest
import VerifiedGarbage.Proof.Bignum.Arm.ExponentTests
import VerifiedGarbage.Proof.Bignum.Arm.ExponentWords
import VerifiedGarbage.Proof.Bignum.Arm.ExportArray
import VerifiedGarbage.Proof.Bignum.Arm.ExportArrayArgs
import VerifiedGarbage.Proof.Bignum.Arm.ExportBE
import VerifiedGarbage.Proof.Bignum.Arm.ExportBEArgs
import VerifiedGarbage.Proof.Bignum.Arm.ExportBECT
import VerifiedGarbage.Proof.Bignum.Arm.ExportEncoding
import VerifiedGarbage.Proof.Bignum.Arm.ExportMasked
import VerifiedGarbage.Proof.Bignum.Arm.FinishArgs
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.HeaderStore
import VerifiedGarbage.Proof.Bignum.Arm.ImportArray
import VerifiedGarbage.Proof.Bignum.Arm.ImportArrayCT
import VerifiedGarbage.Proof.Bignum.Arm.ImportArrayLayout
import VerifiedGarbage.Proof.Bignum.Arm.ImportArraySwap
import VerifiedGarbage.Proof.Bignum.Arm.ImportModulus
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperand
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperandCT
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperandLayout
import VerifiedGarbage.Proof.Bignum.Arm.InitInverse
import VerifiedGarbage.Proof.Bignum.Arm.InitInverseCT
import VerifiedGarbage.Proof.Bignum.Arm.InitMetaMemory
import VerifiedGarbage.Proof.Bignum.Arm.InputCompare
import VerifiedGarbage.Proof.Bignum.Arm.InputCompareArgs
import VerifiedGarbage.Proof.Bignum.Arm.InputCompareCT
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
import VerifiedGarbage.Proof.Bignum.Arm.LoadBECT
import VerifiedGarbage.Proof.Bignum.Arm.LoadBEFn
import VerifiedGarbage.Proof.Bignum.Arm.LoadBEFnArgs
import VerifiedGarbage.Proof.Bignum.Arm.LoadBEFnCT
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Bignum.Arm.MaskByteStep
import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.MaskOutput
import VerifiedGarbage.Proof.Bignum.Arm.MaskOutputArgs
import VerifiedGarbage.Proof.Bignum.Arm.MergeAcceptance
import VerifiedGarbage.Proof.Bignum.Arm.MergeAcceptanceCT
import VerifiedGarbage.Proof.Bignum.Arm.MergeAcceptanceLayout
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
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.MontOpArgs
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
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
import VerifiedGarbage.Proof.Bignum.Arm.PcPrepare
import VerifiedGarbage.Proof.Bignum.Arm.PcValid
import VerifiedGarbage.Proof.Bignum.Arm.PdAccept
import VerifiedGarbage.Proof.Bignum.Arm.PdAcceptCT
import VerifiedGarbage.Proof.Bignum.Arm.PdAccepted
import VerifiedGarbage.Proof.Bignum.Arm.PdApply
import VerifiedGarbage.Proof.Bignum.Arm.PdApplyCT
import VerifiedGarbage.Proof.Bignum.Arm.PdBody
import VerifiedGarbage.Proof.Bignum.Arm.PdBodyCT
import VerifiedGarbage.Proof.Bignum.Arm.PdCheckFirst
import VerifiedGarbage.Proof.Bignum.Arm.PdCheckedCT
import VerifiedGarbage.Proof.Bignum.Arm.PdChecks
import VerifiedGarbage.Proof.Bignum.Arm.PdChecksCT
import VerifiedGarbage.Proof.Bignum.Arm.PdContract
import VerifiedGarbage.Proof.Bignum.Arm.PdContractInput
import VerifiedGarbage.Proof.Bignum.Arm.PdControls
import VerifiedGarbage.Proof.Bignum.Arm.PdControlsCT
import VerifiedGarbage.Proof.Bignum.Arm.PdEntry
import VerifiedGarbage.Proof.Bignum.Arm.PdEntryCT
import VerifiedGarbage.Proof.Bignum.Arm.PdEntryMemory
import VerifiedGarbage.Proof.Bignum.Arm.PdEntryReady
import VerifiedGarbage.Proof.Bignum.Arm.PdFail
import VerifiedGarbage.Proof.Bignum.Arm.PdFailCT
import VerifiedGarbage.Proof.Bignum.Arm.PdFinish
import VerifiedGarbage.Proof.Bignum.Arm.PdFinishCT
import VerifiedGarbage.Proof.Bignum.Arm.PdFn
import VerifiedGarbage.Proof.Bignum.Arm.PdFnCT
import VerifiedGarbage.Proof.Bignum.Arm.PdImportCT
import VerifiedGarbage.Proof.Bignum.Arm.PdImported
import VerifiedGarbage.Proof.Bignum.Arm.PdImportedCT
import VerifiedGarbage.Proof.Bignum.Arm.PdInputImport
import VerifiedGarbage.Proof.Bignum.Arm.PdInputImportCT
import VerifiedGarbage.Proof.Bignum.Arm.PdInverse
import VerifiedGarbage.Proof.Bignum.Arm.PdOdd
import VerifiedGarbage.Proof.Bignum.Arm.PdOddCT
import VerifiedGarbage.Proof.Bignum.Arm.PdOddFinish
import VerifiedGarbage.Proof.Bignum.Arm.PdOddRead
import VerifiedGarbage.Proof.Bignum.Arm.PdParity
import VerifiedGarbage.Proof.Bignum.Arm.PdPrepare
import VerifiedGarbage.Proof.Bignum.Arm.PdPrepareCT
import VerifiedGarbage.Proof.Bignum.Arm.PdPush
import VerifiedGarbage.Proof.Bignum.Arm.PdWritten
import VerifiedGarbage.Proof.Bignum.Arm.Precompute
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeInverse
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOut
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOutArgs
import VerifiedGarbage.Proof.Bignum.Arm.PrepareZero
import VerifiedGarbage.Proof.Bignum.Arm.ProductArgs
import VerifiedGarbage.Proof.Bignum.Arm.ProductStage
import VerifiedGarbage.Proof.Bignum.Arm.PublicAccepted
import VerifiedGarbage.Proof.Bignum.Arm.PublicArgs
import VerifiedGarbage.Proof.Bignum.Arm.PublicArgsCT
import VerifiedGarbage.Proof.Bignum.Arm.PublicEntry
import VerifiedGarbage.Proof.Bignum.Arm.PublicEntryReady
import VerifiedGarbage.Proof.Bignum.Arm.PublicFail
import VerifiedGarbage.Proof.Bignum.Arm.PublicPush
import VerifiedGarbage.Proof.Bignum.Arm.PublicSaved
import VerifiedGarbage.Proof.Bignum.Arm.PublicStackFrame
import VerifiedGarbage.Proof.Bignum.Arm.PublicWritten
import VerifiedGarbage.Proof.Bignum.Arm.QuotientStage
import VerifiedGarbage.Proof.Bignum.Arm.R2CT
import VerifiedGarbage.Proof.Bignum.Arm.R2Constants
import VerifiedGarbage.Proof.Bignum.Arm.R2CountInit
import VerifiedGarbage.Proof.Bignum.Arm.R2Init
import VerifiedGarbage.Proof.Bignum.Arm.ReadPrefix
import VerifiedGarbage.Proof.Bignum.Arm.ReduceChoice
import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
import VerifiedGarbage.Proof.Bignum.Arm.ReductionStage
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.RestoreSlots
import VerifiedGarbage.Proof.Bignum.Arm.ReverseBuffer
import VerifiedGarbage.Proof.Bignum.Arm.ReverseByteStep
import VerifiedGarbage.Proof.Bignum.Arm.ReverseBytesCT
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
import VerifiedGarbage.Proof.Bignum.Arm.RowLoopCT
import VerifiedGarbage.Proof.Bignum.Arm.RowStep
import VerifiedGarbage.Proof.Bignum.Arm.SanitizeBit
import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulus
import VerifiedGarbage.Proof.Bignum.Arm.SaveAcceptance
import VerifiedGarbage.Proof.Bignum.Arm.SaveAcceptanceCT
import VerifiedGarbage.Proof.Bignum.Arm.SaveAcceptanceLayout
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
import VerifiedGarbage.Proof.Bignum.Arm.Setup
import VerifiedGarbage.Proof.Bignum.Arm.SetupArgs
import VerifiedGarbage.Proof.Bignum.Arm.SetupCT
import VerifiedGarbage.Proof.Bignum.Arm.SetupFrame
import VerifiedGarbage.Proof.Bignum.Arm.Shift
import VerifiedGarbage.Proof.Bignum.Arm.ShiftArgs
import VerifiedGarbage.Proof.Bignum.Arm.ShiftCT
import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeft
import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeftCT
import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeftStep
import VerifiedGarbage.Proof.Bignum.Arm.ShiftStep
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstLayout
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstLayoutCT
import VerifiedGarbage.Proof.Bignum.Arm.SquareBody
import VerifiedGarbage.Proof.Bignum.Arm.SquareCross
import VerifiedGarbage.Proof.Bignum.Arm.SquareFinish
import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
import VerifiedGarbage.Proof.Bignum.Arm.SquareOpCT
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.StackPair
import VerifiedGarbage.Proof.Bignum.Arm.Store64
import VerifiedGarbage.Proof.Bignum.Arm.StoreBE
import VerifiedGarbage.Proof.Bignum.Arm.Sub
import VerifiedGarbage.Proof.Bignum.Arm.Sub64
import VerifiedGarbage.Proof.Bignum.Arm.Sub64Math
import VerifiedGarbage.Proof.Bignum.Arm.SubAdvance
import VerifiedGarbage.Proof.Bignum.Arm.SubBody
import VerifiedGarbage.Proof.Bignum.Arm.SubCompare
import VerifiedGarbage.Proof.Bignum.Arm.SubRow
import VerifiedGarbage.Proof.Bignum.Arm.SubRowCT
import VerifiedGarbage.Proof.Bignum.Arm.SubStep
import VerifiedGarbage.Proof.Bignum.Arm.WideMath
import VerifiedGarbage.Proof.Bignum.Arm.WideValue
import VerifiedGarbage.Proof.Bignum.Arm.ZeroStep
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.ExponentWords
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Bignum.FoldedPublic
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.ModulusCheckMath
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.PublicWritten
import VerifiedGarbage.Proof.Bignum.ReadPrefix
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
import VerifiedGarbage.Proof.Rsa.Arm.PrivContract
import VerifiedGarbage.Proof.Rsa.Arm.PrivContractInput
import VerifiedGarbage.Proof.Rsa.Arm.PrivCopyArgs
import VerifiedGarbage.Proof.Rsa.Arm.PrivCopyIncoming
import VerifiedGarbage.Proof.Rsa.Arm.PrivCopyRetained
import VerifiedGarbage.Proof.Rsa.Arm.PrivCrtCall
import VerifiedGarbage.Proof.Rsa.Arm.PrivEntryReady
import VerifiedGarbage.Proof.Rsa.Arm.PrivFn
import VerifiedGarbage.Proof.Rsa.Arm.PrivFnCT
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
import VerifiedGarbage.Proof.Rsa.Arm.PrivVerified
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Rsa.ZeroTest32
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.RsaPss.Arm.CtInit
import VerifiedGarbage.Proof.RsaPss.Arm.CtPad
import VerifiedGarbage.Proof.RsaPss.Arm.CtXor
import VerifiedGarbage.Proof.RsaPss.Arm.YDig
import VerifiedGarbage.Proof.RsaPss.Encoding
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaPss.SignCases
import VerifiedGarbage.Proof.Sha256.StateMem
import VerifiedGarbage.Spec.Pbkdf2.Generic

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: the scan's result

The scan's registers (`scanSet_vp`); then `acc` takes in that `DB`'s first
nonzero byte is `0x01` and, if a salt length is expected, that the salt after
it has that length (`acc2`), and its index goes to its slot (`pos_vp`); then
the flags of `any_salt_len = 0` (`anySet_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h : PssHash)

/-- What the scan keeps. -/
abbrev Kd (P : EP) (τ : State) (m : Mem) : Prop :=
  Ka h P τ m ∧ (∀ i < dbN h P, m (sa P.scr (oEm + lo P + i)) = dbF h P τ i) ∧
    ∀ i < h.D, m (sa P.scr (oEm + lo P + dbN h P + i)) = (seedV h P τ).getD i 0

/-- The scan's registers. -/
theorem scanSet_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (U0 h P) (.block scanSet)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kd h P τ s.mem ∧ fits h P ∧ SC h P τ 0 s) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm)
    fun τ s ⟨hc, hk, hd, hh⟩ => ?_
  have hw : WP isa (.block scanSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P) ∧ t.gpr .r1 = BitVec.ofNat 32 0 ∧
      t.gpr .lr = BitVec.ofNat 32 (dbN h P) ∧ t.gpr .r4 = BitVec.ofNat 32 0 ∧ t.gpr .r5 = BitVec.ofNat 32 0 ∧
      t.gpr .r6 = BitVec.ofNat 32 0 - 1 ∧ t.gpr .r7 = BitVec.ofNat 32 0 := by
    prun [scanSet, atDb, atS, addSlot, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, hk.2.2.1.2.1,
      hk.2.2.1.2.2.1, movw_val (show oEm < 2 ^ 16 by decide), movw_val (show 0 < 2 ^ 16 by decide),
      BitVec.add_assoc, BitVec.ofNat_add_ofNat, dpVal]
  refine WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr, r4, r5, r6, r7⟩ =>
    ⟨hc.regs rd wr sp m, m ▸ ⟨hk, hd, hh⟩, hk.2.1, ⟨by rw [r0, Nat.add_zero], r1, by rw [lr, Nat.sub_zero], ?_, ?_, ?_, r7⟩⟩
  · rw [r4]; simp only [pzJ, Nat.not_lt_zero, ite_false]
  · rw [r5]; simp only [vzJ, Nat.not_lt_zero, ite_false]; rfl
  · rw [r6]; simp only [nfJ, Nat.not_lt_zero, ite_false]; decide

/-- `[any_salt_len ≠ 0]`. -/
abbrev anyW (P : EP) : BitVec 32 := if P.any = 0 then 0 else 1

/-- The index of `DB`'s first nonzero byte, 0 if none. -/
abbrev pzF (P : EP) (τ : State) : Nat := pzJ h P τ (dbN h P)

/-- `acc` after the scan. -/
abbrev acc2 (P : EP) (τ : State) : BitVec 32 :=
  (accW P τ ||| ((vzJ h P τ (dbN h P)).setWidth 32 ^^^ (1 : BitVec 32) ||| nfJ h P τ (dbN h P) >>> 31)) |||
    ((BitVec.ofNat 32 (dbN h P) - BitVec.ofNat 32 (pzF h P τ) - 1 ^^^ BitVec.ofNat 32 P.slt) &&& (anyW P - 1))

/-- What the paths after the scan keep. -/
abbrev K2 (P : EP) (τ : State) (m : Mem) : Prop :=
  In h.D P τ ∧ fits h P ∧ Bm h P m ∧ (∀ i < dbN h P, m (sa P.scr (oEm + lo P + i)) = dbF h P τ i) ∧
    (∀ i < h.D, m (sa P.scr (oEm + lo P + dbN h P + i)) = (seedV h P τ).getD i 0) ∧
    m.readW ((P.lay h.D).fr sPos) 32 = BitVec.ofNat 32 (pzF h P τ) ∧
    m.readW ((P.lay h.D).fr sAcc) 32 = acc2 h P τ

theorem posChk_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r12])
    (.block posChk) hc).isSome = true := ⟨_, by taint_decide⟩

/-- `acc` and `pos` to their slots. -/
theorem pos_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kd h P τ s.mem ∧ fits h P ∧ SC h P τ (dbN h P) s)
      (.seq (.block posSet) (.block posChk))
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  refine VP.seq (G := fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Kd h P τ s.mem ∧ fits h P) ∧
      s.gpr .r4 = BitVec.ofNat 32 (pzF h P τ) ∧ s.gpr .r5 = (vzJ h P τ (dbN h P)).setWidth 32 ∧
      s.gpr .r6 = nfJ h P τ (dbN h P) ∧
      s.gpr .r1 = accW P τ ∧ s.gpr .r2 = BitVec.ofNat 32 (dbN h P) ∧ s.gpr .r3 = BitVec.ofNat 32 P.slt ∧
      s.gpr .r8 = anyW P ∧ s.gpr .r12 = P.B)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hk, hf, hs⟩ => ?_)
    (VP.taint _ posChk_cert (fun _ _ _ _ h₁ h₂ r hr => ?_)
      fun τ s ⟨⟨hc, hk, hf⟩, r4, r5, r6, r1, r2, r3, r8, r12⟩ => ?_)
  · have hi := hk.1.1
    obtain ⟨a7, ra7, va7⟩ := argAt hi hc.st (j := 7) (by decide)
    replace va7 : s.mem.readW ((P.lay h.D).fr (arg 7)) 32 = BitVec.ofNat 32 P.slt := va7
    have hw : WP isa (.block posSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r4 = BitVec.ofNat 32 (pzF h P τ) ∧ t.gpr .r5 = (vzJ h P τ (dbN h P)).setWidth 32 ∧
        t.gpr .r6 = nfJ h P τ (dbN h P) ∧
        t.gpr .r1 = accW P τ ∧ t.gpr .r2 = BitVec.ofNat 32 (dbN h P) ∧ t.gpr .r3 = BitVec.ofNat 32 P.slt ∧
        t.gpr .r8 = anyW P ∧ t.gpr .r12 = P.B := by
      prun [posSet, sp0, ld, hc.st.sp, a7, ra7, va7, arg_lt, hc.aFr hg, hc.rFr hg, hk.1.2.2.2, hk.1.2.2.1.2.2.1,
        hk.1.2.2.1.2.2.2, hs.r4, hs.r5, hs.r6]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, t4, t5, t6, t1, t2, t3, t8, t12⟩ =>
      ⟨⟨hc.regs rd wr sp m, m ▸ hk, hf⟩, t4, t5, t6, t1, t2, t3, t8, t12⟩
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.2.2.2.2.2.2, h₂.2.2.2.2.2.2.2.2]
  · have hi := hk.1.1
    have hw : WP isa (.block posChk) s fun t =>
        t.mem = (s.mem.writeW ((P.lay h.D).fr sPos) (BitVec.ofNat 32 (pzF h P τ))).writeW ((P.lay h.D).fr sAcc)
          (acc2 h P τ) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
      prun [posChk, st, r1, r2, r3, r4, r5, r6, r8, r12, slotAt hi (d := sAcc) (by decide),
        slotAt hi (d := sPos) (by decide), hc.st.inFr (d := sAcc) (n := 4) (by show sAcc + 4 ≤ frameBytes; decide),
        hc.st.inFr (d := sPos) (n := 4) (by show sPos + 4 ≤ frameBytes; decide), dpVal]
    refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
    have fr : Frame [slotR (P.lay h.D) sPos, slotR (P.lay h.D) sAcc] s.mem t.mem := by
      rw [m]
      exact (slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))
    obtain ⟨σ', ok⟩ := hg.ok
    have kk : ∀ d, d + 4 ≤ frameBytes → (d + 4 ≤ sAcc ∨ sPos + 4 ≤ d) →
        t.mem.readW ((P.lay h.D).fr d) 32 = s.mem.readW ((P.lay h.D).fr d) 32 := fun d hd hd' => by
      rw [m, slot_ww _ _ hd (by decide) (by unfold sAcc sPos at hd'; unfold sAcc; omega),
        slot_ww _ _ hd (by decide) (by unfold sAcc sPos at hd'; unfold sPos; omega)]
    have kb : ∀ o, o + 1 ≤ oRsa → t.mem (sa P.scr o) = s.mem (sa P.scr o) := fun o ho =>
      fr _ fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (hg.slot ok (o := o) (n := 1) (by omega) (by rw [hg.F]; decide)).symm _ (Region.contains_self _ _)
        · exact (hg.slot ok (o := o) (n := 1) (by omega) (by rw [hg.F]; decide)).symm _ (Region.contains_self _ _)
    obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi hf
    have e1 : oEm = 1024 := rfl
    have e2 : oRsa = 8192 := rfl
    refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, hi, hf,
      ⟨by rw [kk _ (by decide) (by decide)]; exact hk.1.2.2.1.1, by rw [kk _ (by decide) (by decide)]; exact hk.1.2.2.1.2.1,
        by rw [kk _ (by decide) (by decide)]; exact hk.1.2.2.1.2.2.1,
        by rw [kk _ (by decide) (by decide)]; exact hk.1.2.2.1.2.2.2⟩,
      fun i hi' => by rw [kb _ (by omega)]; exact hk.2.1 i hi',
      fun i hi' => by rw [kb _ (by omega)]; exact hk.2.2 i hi', ?_, by rw [m, Mem.readW_writeW_self32]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact slotW hg (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
    · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]

/-- The flags of `any_salt_len = 0`. -/
theorem anySet_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem) (.block anySet)
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem) ∧ s.z = decide (P.any = 0)) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hk⟩ => ?_
  have hw : WP isa (.block anySet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.z = decide (P.any = 0) := by
    prun [anySet, sp0, ld, hc.st.sp, hc.aFr hg, hc.rFr hg, hk.2.2.1.2.2.2]
    by_cases e : P.any = 0#32 <;> simp [e]
  exact WP.mono hw fun t ⟨m, rd, wr, sp, z⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hk⟩, z⟩

end VG.Proof.RsaPss.Arm.Vf
