module

public import VerifiedGarbage.Proof.RsaOaep.Arm.DecCall
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Impl.RsaOaep.Arm
import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
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
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.TaintErase
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.MdStream.Arm.Words
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Calls
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
import VerifiedGarbage.Proof.RsaOaep.Arm.Label
import VerifiedGarbage.Proof.RsaOaep.Decode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.RsaPss.Arm.CtMgfLoop
import VerifiedGarbage.Proof.RsaPss.Arm.CtPad
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Sha256.StateMem

/-!
# RSAES-OAEP decryption on ARMv7: the check of `k`, and when it fails

`chk_vp`: the private-key operation's result to its slot, and the flags of
`k < 2 hLen + 2`. `fail_vp`: then zeros to `out` and to `*msg_len`, and the
result `(r = 2) ? 2 : 0`, as `decrypt` says (`Proof.RsaOaep.decOut_short`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Dec

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa arg)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

/-- The flags of `k < c`: zero exactly when `c ≤ k`. -/
theorem top_z {K c : Nat} (hK : K ≤ 1024) (hc : c ≤ 1024) :
    ((BitVec.ofNat 32 K - BitVec.ofNat 32 c) >>> 31 - 0 == 0) = decide (c ≤ K) := by
  simp only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero]
  by_cases h : c ≤ K
  · rw [Offset.ofNat_sub_ofNat (w := 32) h, decide_eq_true h]
    apply beq_iff_eq.mpr
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; simp; omega
  · rw [decide_eq_false h]
    apply beq_false_of_ne
    intro e
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (a := K) (by omega), Nat.mod_eq_of_lt (a := c) (by omega)] at this
    simp at this; omega

/-- Bytes of our part of `scratch` from its start, kept by a frame that misses them. -/
theorem em_keep {scr : BitVec 32} {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint (sR scr 0 n) r) (hn : n < 2 ^ 64) {f : Nat → Byte}
    (h : ∀ i < n, m (sa scr i) = f i) : ∀ i < n, m' (sa scr i) = f i := by
  have := sbytes_keep (scr := scr) hf hd (by omega) (f := f) (fun i hi => by rw [Nat.zero_add]; exact h i hi)
  intro i hi; have e := this i hi; rwa [Nat.zero_add] at e

/-- After the check. -/
abbrev C2 (D : Nat) (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ In P σ ∧ (∀ i < P.K, s.mem (sa P.scr i) = V P σ i) ∧
    s.mem.readW (P.lay.fr sRes) 32 = rV P σ ∧ OcK P σ ∧ s.z = decide (2 * D + 2 ≤ P.K)

theorem chk_vp (h : OHash) (P : EP) : VP (R2 P) (.block (decChk h.H)) (C2 h.H.D P) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm)
    fun σ s ⟨hc, hi, he, r0, hk⟩ => ?_
  have hg := hi.geo
  have hD := h.D_le
  have hK := hi.k1024
  obtain ⟨σ', ok⟩ := hg.ok
  obtain ⟨a4, r4, v4⟩ := argAt hi hc.st (j := 4) (by decide)
  replace v4 : s.mem.readW (P.lay.fr (arg 4)) 32 = BitVec.ofNat 32 P.K := v4
  have k4 : ∀ v : BitVec 32, (s.mem.writeW (P.lay.fr sRes) v).readW (P.lay.fr (arg 4)) 32 =
      s.mem.readW (P.lay.fr (arg 4)) 32 := fun v => Lay.readW_fr_other _ _ _ (by
    unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes sRes; simp) (by decide) (by decide)
  have hw : WP isa (.block (decChk h.H)) s fun t => t.mem = s.mem.writeW (P.lay.fr sRes) (rV P σ) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.z = decide (2 * h.H.D + 2 ≤ P.K) := by
    prun [decChk, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.wFr hg, a4, r4, v4, k4, r0, sRes_lt, arg_lt,
      movw_val (show 2 * h.H.D + 2 < 2 ^ 16 by omega), dpVal, top_z hK (show 2 * h.H.D + 2 ≤ 1024 by omega)]
  refine WP.mono hw fun t ⟨m, rd, wr, sp, z⟩ => ?_
  have fr : Frame [slotR P.lay sRes] s.mem t.mem := by rw [m]; exact slot_frame _ _ _ _
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, hi, em_keep fr (fun r hr => ?_) (by omega) he,
    by rw [m, Mem.readW_writeW_self32], hk, z⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact slotW hg (by decide)
  · simp only [List.mem_singleton] at hr; subst hr; exact slotSep (by decide) (by decide) (by decide)
  · simp only [List.mem_singleton] at hr; subst hr
    exact (hg.slot ok (o := 0) (n := P.K) (by unfold oRsa; omega) (by rw [hg.F]; decide)).symm

/-! ## When `k` is too short -/

/-- `(r = 2) ? 2 : 0`. -/
abbrev faultV (r : BitVec 32) : BitVec 32 := (((r ^^^ 2) - 1) >>> 31) <<< 1

theorem faultV_rOf (o : Spec.Rsa.Outcome) : faultV (rOf o) = if o = .fault then 2 else 0 := by
  cases o <;> simp only [rOf, reduceCtorEq, ite_false, ite_true] <;> decide

theorem out_wbuf {P : EP} {σ : State} (hi : In P σ) : WBuf P.lay P.out P.K := by
  have hK := hi.k1024
  have hf := hi.ok.fits P.OUT (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hf
  exact ⟨hf, by omega, ⟨P.OUT, by simp, Region.contains_self _ _⟩,
    hi.ok.stk_fr (R := P.OUT) (.inr (by simp)) (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes + 56; decide)⟩

theorem nB_length {P : EP} {σ : State} (hi : In P σ) : P.nB.length = P.K := by
  rw [← hi.nB]; simp [Spec.Rsa.bytesAt]

theorem ctB_length (P : EP) (σ : State) : (ctB P σ).length = P.K := by simp [Spec.Rsa.bytesAt]

/-- A 64-bit word written as two 32-bit halves, the high one zero. -/
theorem readW_pair (m : Mem) (a : Addr) {L : Nat} (hL : L < 2 ^ 32) :
    ((m.writeW a (BitVec.ofNat 32 L)).writeW (a + BitVec.ofNat 64 4) (0 : BitVec 32)).readW a 64 =
      BitVec.ofNat 64 L := by
  show (Mem.read _ a 8).setWidth 64 = _
  rw [Mem.read_eq_of_bytes (n := 8) (v := BitVec.ofNat 64 L) fun i hi => ?_]
  · exact BitVec.setWidth_eq _
  by_cases h4 : i < 4
  · have e1 : ¬ (a + BitVec.ofNat 64 i - (a + BitVec.ofNat 64 4)).toNat < 32 / 8 := by
      rw [show a + BitVec.ofNat 64 i - (a + BitVec.ofNat 64 4) = BitVec.ofNat 64 i - BitVec.ofNat 64 4 by
        rw [Offset.add_sub_add_left]]
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    simp only [Mem.writeW]
    rw [Mem.write_apply e1]
    simp only [Mem.write, Mem.sub_ofNat_toNat a (by omega : i < 2 ^ 64), show i < 32 / 8 by omega, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show L < 2 ^ (8 * (32 / 8)) from hL),
      Nat.mod_eq_of_lt (show L < 2 ^ (8 * 8) from Nat.lt_of_lt_of_le hL (by decide))]
    rw [show 8 * (32 / 8) = 32 from rfl, Nat.mod_eq_of_lt hL]
  · have e : a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 4 + BitVec.ofNat 64 (i - 4) := by
      rw [Offset.add_add, show 4 + (i - 4) = i by omega]
    simp only [Mem.writeW, Mem.write]
    rw [e, Mem.sub_ofNat_toNat _ (by omega : i - 4 < 2 ^ 64)]
    simp only [show i - 4 < 32 / 8 by omega, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    have : 2 ^ 32 ≤ 2 ^ (8 * i) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.div_eq_of_lt (by omega : L % 2 ^ 64 < 2 ^ (8 * i))]
    simp

theorem ml_fit {P : EP} {σ : State} (hi : In P σ) : P.ml.toNat + 8 ≤ 2 ^ 32 := by
  have := hi.ok.fits P.ML (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this

theorem mlStore_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r1]) (.block mlStore) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `*msg_len := r3 (low), r2 (high)`, through `r1 = msg_len`. -/
theorem mlStore_vp (P : EP) {F : State → State → Prop} (hF : ∀ σ s, F σ s → S P σ s ∧ s.gpr .r1 = P.ml)
    {G : State → State → Prop}
    (hG : ∀ σ s (m : Mem), F σ s → Frame [P.ML] s.mem m →
      m.readW (State.addr P.ml) 64 = BitVec.ofNat 64 (s.gpr .r3).toNat →
      F σ { s with mem := m } → G σ { s with mem := m })
    (hF' : ∀ σ s (m : Mem), F σ s → Frame [P.ML] s.mem m → F σ { s with mem := m })
    (h2 : ∀ σ s, F σ s → s.gpr .r2 = 0) :
    VP F (.block mlStore) G := by
  refine VP.taint _ mlStore_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    rw [(hF _ _ h₁).2, (hF _ _ h₂).2]
  obtain ⟨⟨hi, st⟩, r1⟩ := hF σ s hs
  have fit := ml_fit hi
  have a0 : State.addr P.ml = State.addr (P.ml + BitVec.ofNat 32 0) := by rw [BitVec.add_zero]
  have a4 : State.addr (P.ml + BitVec.ofNat 32 4) = State.addr P.ml + BitVec.ofNat 64 4 := addr_add (by omega)
  have win : ∀ d, d + 4 ≤ 8 → InRegions s.wr (State.addr P.ml + BitVec.ofNat 64 d) 4 := fun d hd =>
    ⟨P.ML, by rw [st.wr, hi.ok.wr]; simp, Offset.contains_base _ hd (by omega)⟩
  have w0 : InRegions s.wr (State.addr P.ml) 4 := by have := win 0 (by decide); rwa [BitVec.add_zero] at this
  have w4 := win 4 (by decide)
  have hw : WP isa (.block mlStore) s fun t => t.mem = (s.mem.writeW (State.addr P.ml) (s.gpr .r3)).writeW
      (State.addr P.ml + BitVec.ofNat 64 4) (s.gpr .r2) ∧ t = { s with mem := t.mem } := by
    prun [mlStore, r1, a4, w0, w4]
    rfl
  refine WP.mono hw fun t ⟨m, et⟩ => ?_
  have c0 : (⟨State.addr P.ml, 8⟩ : Region).Contains (State.addr P.ml) (32 / 8) := by
    have := Offset.contains_base (State.addr P.ml) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  have fr : Frame [P.ML] s.mem t.mem := by
    rw [m]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (s.gpr .r3) c0).writeW
      (List.mem_singleton_self _) (s.gpr .r2) (Offset.contains_base _ (by decide) (by decide))
  rw [et]
  refine hG σ s t.mem hs fr ?_ (hF' σ s t.mem hs fr)
  have e := readW_pair s.mem (State.addr P.ml) (s.gpr .r3).isLt
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at e
  rw [m, h2 σ s hs]
  exact e

end VG.Proof.RsaOaep.Arm.Dec
