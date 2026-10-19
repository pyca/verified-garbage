module

public import VerifiedGarbage.Proof.RsaOaep.Arm.DecAcc
public import VerifiedGarbage.Proof.RsaPss.VerifyCases
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Impl.RsaOaep.Arm
import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
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
import VerifiedGarbage.Proof.Framework.Offset
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
import VerifiedGarbage.Proof.RsaOaep.Arm.DecFail
import VerifiedGarbage.Proof.RsaOaep.Arm.Label
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.RsaPss.Arm.CtMgfLoop
import VerifiedGarbage.Proof.RsaPss.Arm.CtPad
import VerifiedGarbage.Proof.RsaPss.Encoding
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.RsaPss.SignCases
import VerifiedGarbage.Proof.Sha256.StateMem

/-!
# RSAES-OAEP decryption on ARMv7: the scan of `T`

`scan_vp`: the scan of `n` bytes of our part of `scratch` finds the index
(`pzS`) and the value (`vzS`) of their first byte that is not zero, if any
(`nfS`), without a branch. `tscan_vp`: on `T = DB[hLen..]`, then `acc`
takes in that this byte is `0x01`, and `idx` goes to its slot.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Dec

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa arg sAcc sPos countLoop scanBody)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.X25519.Arm (dpVal)

/-! ## The scan -/

section Scan

/-- The bytes, as a list. -/
abbrev sL (n : Nat) (f : Nat → Byte) : List Byte := (List.range n).map f

/-- Where the zeros end. -/
abbrev lzS (n : Nat) (f : Nat → Byte) : Nat := RsaPss.lz (sL n f)

/-- The index and value of the first byte not zero, after `j` bytes, and
whether none was found. -/
abbrev pzS (n : Nat) (f : Nat → Byte) (j : Nat) : Nat := if lzS n f < j then lzS n f else 0
abbrev vzS (n : Nat) (f : Nat → Byte) (j : Nat) : Byte := if lzS n f < j then f (lzS n f) else 0
abbrev nfS (n : Nat) (f : Nat → Byte) (j : Nat) : BitVec 32 := if lzS n f < j then 0 else BitVec.allOnes 32

theorem bz : ∀ b : Byte, (b.setWidth 32 - 1) >>> 31 = if b = 0 then 1 else 0 := by decide

/-- After `j` bytes of the scan of the `n` bytes at `o`. -/
structure SC (scr : BitVec 32) (o n : Nat) (f : Nat → Byte) (j : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = scr + BitVec.ofNat 32 (o + j)
  r1 : s.gpr .r1 = BitVec.ofNat 32 j
  lr : s.gpr .lr = BitVec.ofNat 32 (n - j)
  r4 : s.gpr .r4 = BitVec.ofNat 32 (pzS n f j)
  r5 : s.gpr .r5 = (vzS n f j).setWidth 32
  r6 : s.gpr .r6 = nfS n f j
  r7 : s.gpr .r7 = 0

theorem scanBody_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1, .lr])
    (.block scanBody) hc).isSome = true := ⟨_, by taint_decide⟩

theorem sL_getD {n : Nat} {f : Nat → Byte} {j : Nat} (hj : j < n) : (sL n f).getD j 0 = f j := by
  simp [sL, List.getD_eq_getElem?_getD, hj]

theorem sL_length (n : Nat) (f : Nat → Byte) : (sL n f).length = n := by simp [sL]

theorem lzS_le (n : Nat) (f : Nat → Byte) : lzS n f ≤ n := by
  have e := RsaPss.lz_le (sL n f); rwa [sL_length] at e

/-- One byte of the scan. -/
theorem scan_step {n : Nat} {f : Nat → Byte} {j : Nat} (hj : j < n) (b : Byte) (hb : b = f j) :
    let r3 : BitVec 32 := if b = 0 then 1 else 0
    let r8 := (r3 - 1) &&& nfS n f j
    BitVec.ofNat 32 (pzS n f j) ||| BitVec.ofNat 32 j &&& r8 = BitVec.ofNat 32 (pzS n f (j + 1)) ∧
    (vzS n f j).setWidth 32 ||| b.setWidth 32 &&& r8 = (vzS n f (j + 1)).setWidth 32 ∧
    nfS n f j &&& (0 - r3) = nfS n f (j + 1) := by
  intro r3 r8
  have az : ∀ x : BitVec 32, x &&& 0 = 0 := fun x => BitVec.and_zero
  have za : ∀ x : BitVec 32, 0 &&& x = 0 := fun x => BitVec.zero_and
  have oz : ∀ x : BitVec 32, x ||| 0 = x := fun x => BitVec.or_zero
  have zo : ∀ x : BitVec 32, 0 ||| x = x := fun x => BitVec.zero_or
  have hlt := lzS_le n f
  rcases Nat.lt_trichotomy (lzS n f) j with hl | hl | hl
  · have h8 : r8 = 0 := by simp only [r8, nfS, ite_eq_left hl, az]
    simp only [h8, az, oz, pzS, vzS, nfS, ite_eq_left hl, ite_eq_left (by omega : lzS n f < j + 1), za]
    exact ⟨trivial, trivial, trivial⟩
  · have hne : b ≠ 0 := by
      rw [hb, ← hl, ← sL_getD (n := n) (f := f) (by omega)]
      exact RsaPss.getD_lz_ne (by rw [sL_length]; show lzS n f < n; omega)
    have h3 : r3 = 0 := by simp only [r3, hne, ite_false]
    have h8 : r8 = BitVec.allOnes 32 := by
      simp only [r8, h3, nfS, ite_eq_right (show ¬ lzS n f < j by omega)]; decide
    simp only [h8, h3, BitVec.and_allOnes, pzS, vzS, nfS, ite_eq_right (show ¬ lzS n f < j by omega),
      ite_eq_left (show lzS n f < j + 1 by omega)]
    have sz : (0 : Byte).setWidth 32 = 0 := rfl
    refine ⟨by rw [hl, BitVec.zero_or], by rw [hl, hb, sz, zo], by decide⟩
  · have hz : b = 0 := by rw [hb, ← sL_getD (n := n) (f := f) hj]; exact RsaPss.getD_lt_lz hl
    have h3 : r3 = 1 := by simp only [r3, hz, ite_true]
    have h8 : r8 = 0 := by
      simp only [r8, h3]; rw [show (1 : BitVec 32) - 1 = 0 by decide, za]
    simp only [h8, h3, az, oz, pzS, vzS, nfS, ite_eq_right (show ¬ lzS n f < j by omega),
      ite_eq_right (show ¬ lzS n f < j + 1 by omega)]
    exact ⟨trivial, trivial, by decide⟩

variable {L : Lay} {scr : BitVec 32}

/-- The scan of the `n` bytes at `o`. -/
theorem scan_vp (hg : Geo L scr) {o n : Nat} (ho : o + n ≤ oRsa) (hn : 0 < n) {f : State → Nat → Byte}
    {X : State → Mem → Prop} (hX : ∀ σ m, X σ m → ∀ i < n, m (sa scr (o + i)) = f σ i) :
    VP (fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ SC scr o n (f σ) 0 s)
      (countLoop scanBody)
      (fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ SC scr o n (f σ) n s) := by
  have e2 : oRsa = 8192 := rfl
  have fit := hg.fit
  let I : Nat → State → State → Prop := fun k σ s => k ≤ n ∧ Ctx L scr σ s ∧ X σ s.mem ∧
    SC scr o n (f σ) (n - k) s
  refine (VP.loop (I := I) (fun k => ?_) (n - 1)).mono (fun σ s ⟨hc, hx, hs⟩ => ⟨by omega, hc, hx,
    by rw [show n - (n - 1 + 1) = 0 by omega]; exact hs⟩) fun _ _ h => h
  refine VP.taint _ scanBody_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hk, hc, hx, hs⟩ => ?_
  · obtain ⟨-, -, -, p₁⟩ := h₁
    obtain ⟨-, -, -, p₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [p₁.r0, p₂.r0]
    · rw [p₁.r1, p₂.r1]
    · rw [p₁.lr, p₂.lr]
  generalize hj : n - (k + 1) = j at hs
  have hjn : j < n := by omega
  have ad : State.addr (scr + BitVec.ofNat 32 (o + j)) = sa scr (o + j) := hg.addr (by omega)
  have rd : InRegions (s.rd ++ s.wr) (sa scr (o + j)) 1 := hg.rd hc.st (by omega)
  have lr1 : BitVec.ofNat 32 (n - j) - 1 = BitVec.ofNat 32 (n - (j + 1)) := by
    rw [show n - j = (n - (j + 1)) + 1 by omega]; exact sub_one_ofNat (by omega)
  have hw : WP isa (.block scanBody) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.gpr .r0 = scr + BitVec.ofNat 32 (o + (j + 1)) ∧ t.gpr .r1 = BitVec.ofNat 32 (j + 1) ∧
      t.gpr .lr = BitVec.ofNat 32 (n - (j + 1)) ∧
      t.gpr .r4 = BitVec.ofNat 32 (pzS n (f σ) j) ||| BitVec.ofNat 32 j &&&
        ((if f σ j = 0 then 1 else 0) - 1 &&& nfS n (f σ) j) ∧
      t.gpr .r5 = (vzS n (f σ) j).setWidth 32 ||| (f σ j).setWidth 32 &&&
        ((if f σ j = 0 then 1 else 0) - 1 &&& nfS n (f σ) j) ∧
      t.gpr .r6 = nfS n (f σ) j &&& (0 - if f σ j = 0 then 1 else 0) ∧ t.gpr .r7 = 0 ∧
      t.z = decide (n - (j + 1) = 0) := by
    prun [scanBody, hs.r0, hs.r1, hs.lr, hs.r4, hs.r5, hs.r6, hs.r7, ad, rd, hX σ s.mem hx j hjn, bz, lr1, dpVal]
    refine ⟨?_, ?_, ?_⟩
    · rw [BitVec.add_assoc, VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32, Nat.add_assoc]
    · exact VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32 _
    · rw [VG.Proof.X25519.Arm.ofNat_beq_zero (by omega)]
  refine WP.mono hw fun t ⟨m, rd', wr, sp, r0, r1, lr, r4, r5, r6, r7, z⟩ => ?_
  have st := scan_step hjn _ rfl (f := f σ)
  have hc' : Ctx L scr σ t := hc.regs rd' wr sp m
  have hx' : X σ t.mem := m ▸ hx
  have sk : SC scr o n (f σ) (j + 1) t :=
    ⟨r0, r1, lr, by rw [r4]; exact st.1, by rw [r5]; exact st.2.1, by rw [r6]; exact st.2.2, r7⟩
  refine ⟨by rw [VG.Proof.X25519.Arm.eval_ne, z, show n - (j + 1) = k by omega]; cases k <;> simp,
    fun h0 => ⟨hc', hx', by obtain rfl : n = j + 1 := (by omega); exact sk⟩,
    fun hpos => ⟨by omega, hc', hx', by rw [show n - k = j + 1 by omega]; exact sk⟩⟩

end Scan

/-! ## `T` -/

variable (h g : OHash)

/-- `T = DB[hLen..]`, its length, and the index after its first byte not zero. -/
abbrev tN (P : EP) : Nat := P.K - (2 * h.H.D + 1)
abbrev T (P : EP) (σ : State) (j : Nat) : Byte := V5 h g P σ (1 + 2 * h.H.D + j)
abbrev idx (P : EP) (σ : State) : Nat := pzS (tN h P) (T h g P σ) (tN h P)

/-- The decoding's checks all pass. -/
abbrev allOk (P : EP) (σ : State) : Prop :=
  hdOk h g P σ ∧ lzS (tN h P) (T h g P σ) < tN h P ∧ T h g P σ (lzS (tN h P) (T h g P σ)) = 1

/-- After the scan. -/
abbrev A2 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ Y h g P σ s.mem ∧
    (∃ a : BitVec 32, s.mem.readW (P.lay.fr sAcc) 32 = a ∧ a.toNat < 256 ∧ (a = 0 ↔ allOk h g P σ)) ∧
    s.mem.readW (P.lay.fr sPos) 32 = BitVec.ofNat 32 (idx h g P σ)

theorem endB : ∀ b : Byte, (((b.setWidth 32 ^^^ (1 : BitVec 32)) ||| (0 : BitVec 32) >>> 31).toNat < 256 ∧
    (((b.setWidth 32 ^^^ (1 : BitVec 32)) ||| (0 : BitVec 32) >>> 31) = 0 ↔ b = 1)) := by decide

/-- What the end of the scan adds to `acc`. -/
theorem endX (c : Prop) [Decidable c] (b : Byte) :
    (((if c then b else 0).setWidth 32 ^^^ (1 : BitVec 32)) |||
      (if c then (0 : BitVec 32) else BitVec.allOnes 32) >>> 31).toNat < 256 ∧
    ((((if c then b else 0).setWidth 32 ^^^ (1 : BitVec 32)) |||
      (if c then (0 : BitVec 32) else BitVec.allOnes 32) >>> 31) = 0 ↔
      c ∧ b = 1) := by
  by_cases hc : c
  · simp only [hc, ite_true, true_and]
    exact endB b
  · simp only [hc, ite_false, false_and, iff_false]
    exact ⟨by decide, by decide⟩

theorem tscan_vp (P : EP) :
    VP (A1 h g P) (.seq (.block (scanSet h.H)) (.seq (countLoop scanBody) (.block scanEnd))) (A2 h g P) := by
  by_cases hP : ∃ σ, In P σ ∧ 2 * h.H.D + 2 ≤ P.K
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1.1.1.1, hs.2.1.1.1.2.1⟩
  obtain ⟨σ₀, hi₀, hfit⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hi₀.k1024
  have hD := h.D_le
  have hD0 := h.D_pos
  have htN : tN h P = P.K - (2 * h.H.D + 1) := rfl
  let X : State → Mem → Prop := fun σ m => Y h g P σ m ∧ ∃ a : BitVec 32, m.readW (P.lay.fr sAcc) 32 = a ∧
    a.toNat < 256 ∧ (a = 0 ↔ hdOk h g P σ)
  refine VP.seq (G := fun σ s => Ctx P.lay P.scr σ s ∧ X σ s.mem ∧
      SC P.scr (oEm + 1 + 2 * h.H.D) (tN h P) (T h g P σ) 0 s)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hy, ha⟩ => ?_)
    (VP.seq (scan_vp hg (o := oEm + 1 + 2 * h.H.D) (n := tN h P) (by oomega) (by omega) (f := T h g P) (X := X)
      fun σ m hx i hi => by rw [show oEm + 1 + 2 * h.H.D + i = 1 + 2 * h.H.D + i by oomega]; exact hx.1.2 _ (by omega))
      ?_)
  · have hi := hy.1.1.1
    obtain ⟨a4, r4, v4⟩ := argAt hi hc.st (j := 4) (by decide)
    replace v4 : s.mem.readW (P.lay.fr (arg 4)) 32 = BitVec.ofNat 32 P.K := v4
    have hw : WP isa (.block (scanSet h.H)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.sp = s.sp ∧ t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + 1 + 2 * h.H.D) ∧ t.gpr .r1 = 0 ∧
        t.gpr .lr = BitVec.ofNat 32 (tN h P) ∧ t.gpr .r4 = 0 ∧ t.gpr .r5 = 0 ∧ t.gpr .r6 = BitVec.allOnes 32 ∧
        t.gpr .r7 = 0 := by
      prun [scanSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a4, r4, v4, arg_lt,
        movw_val (show oEm + 1 + 2 * h.H.D < 2 ^ 16 by oomega), movw_val (show 2 * h.H.D + 1 < 2 ^ 16 by omega),
        movw_val (show 0 < 2 ^ 16 by decide), Offset.ofNat_sub_ofNat (show 2 * h.H.D + 1 ≤ P.K by omega), dpVal]
      decide
    refine WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr, r4', r5, r6, r7⟩ =>
      ⟨hc.regs rd wr sp m, m ▸ ⟨hy, ha⟩, ⟨by rw [r0]; rfl, r1, by rw [lr, Nat.sub_zero], ?_, ?_, ?_, r7⟩⟩
    · rw [r4']; simp only [pzS, Nat.not_lt_zero, ite_false]; rfl
    · rw [r5]; simp only [vzS, Nat.not_lt_zero, ite_false]; rfl
    · rw [r6]; simp only [nfS, Nat.not_lt_zero, ite_false]
  -- `acc` and `idx` to their slots.
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm)
    fun σ s ⟨hc, ⟨hy, a, ha, hab, hae⟩, hs⟩ => ?_
  have hi := hy.1.1.1
  have ex := endX (lzS (tN h P) (T h g P σ) < tN h P) (T h g P σ (lzS (tN h P) (T h g P σ)))
  have hw : WP isa (.block scanEnd) s fun t =>
      t.mem = (s.mem.writeW (P.lay.fr sAcc) (a ||| (((vzS (tN h P) (T h g P σ) (tN h P)).setWidth 32 ^^^ (1 : BitVec 32)) |||
        nfS (tN h P) (T h g P σ) (tN h P) >>> 31))).writeW (P.lay.fr sPos) (BitVec.ofNat 32 (idx h g P σ)) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [scanEnd, sp0, ld, st, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.wFr hg, ha, hs.r4, hs.r5, hs.r6, dpVal,
      slot_ww _ _ (show sAcc + 4 ≤ frameBytes by decide) (show sPos + 4 ≤ frameBytes by decide) (by decide)]
  refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
  have fr : Frame [slotR P.lay sAcc, slotR P.lay sPos] s.mem t.mem := by
    rw [m]; exact ((slot_frame _ _ _ _).mono (by simp)).trans ((slot_frame _ _ _ _).mono (by simp))
  have dS : ∀ o n, o + n ≤ oRsa → ∀ r ∈ [slotR P.lay sAcc, slotR P.lay sPos], (sR P.scr o n).Disjoint r := by
    intro o n hon r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
  have hx : (((vzS (tN h P) (T h g P σ) (tN h P)).setWidth 32 ^^^ (1 : BitVec 32)) |||
      nfS (tN h P) (T h g P σ) (tN h P) >>> 31).toNat < 256 ∧
      ((((vzS (tN h P) (T h g P σ) (tN h P)).setWidth 32 ^^^ (1 : BitVec 32)) |||
        nfS (tN h P) (T h g P σ) (tN h P) >>> 31) = 0 ↔
        lzS (tN h P) (T h g P σ) < tN h P ∧ T h g P σ (lzS (tN h P) (T h g P σ)) = 1) := ex
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, ⟨⟨hy.1.1.keep h fr fun r hr => ?_,
    hy.1.2.1.keep h fr (dS _ _ (by oomega)), ?_⟩, em_keep fr (dS _ _ (by oomega)) (by omega) hy.2⟩,
    ⟨_, by rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32], ?_, ?_⟩,
    by rw [m, Mem.readW_writeW_self32]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · rw [← hy.1.2.2]
    exact em_keep (n := 1) fr (dS _ _ (by oomega)) (by decide)
      (f := fun _ => s.mem (sa P.scr 0)) (fun i hi => by rw [show i = 0 by omega]) 0 (by decide)
  · rw [BitVec.toNat_or]; exact Nat.or_lt_two_pow (n := 8) hab hx.1
  · rw [or_eq_zero32, hae, hx.2]

end VG.Proof.RsaOaep.Arm.Dec
