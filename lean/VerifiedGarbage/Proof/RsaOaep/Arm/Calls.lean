module

public import VerifiedGarbage.Impl.RsaOaep.Arm
import VerifiedGarbage.Proof.RsaPss.Arm.CtXor
import VerifiedGarbage.Proof.RsaPss.Arm.CtInit
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Upd
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Impl.RsaOaep.Arm
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
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
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
import VerifiedGarbage.Proof.Mgf1.Basic
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
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.RsaPss.Arm.CtHash
import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
import VerifiedGarbage.Proof.RsaPss.Arm.CtPad
import VerifiedGarbage.Proof.Sha256.StateMem
public meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtXor
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtInit
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Upd
meta import Init.Data.Nat.Bitwise.Basic
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
meta import VerifiedGarbage.Proof.Mgf1.Basic
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Pbkdf2.Memory
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Calls
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
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtHash
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtPad
meta import VerifiedGarbage.Proof.Sha256.StateMem
import VerifiedGarbage.Proof.RsaPss.Arm.Step
meta import VerifiedGarbage.Proof.RsaPss.Arm.Step
public import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Hash
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Hash
public import VerifiedGarbage.Proof.RsaPss.Arm.Prims
meta import VerifiedGarbage.Proof.RsaPss.Arm.Prims
public import VerifiedGarbage.Proof.RsaPss.Arm.Base
meta import VerifiedGarbage.Proof.RsaPss.Arm.Base

/-!
# RSAES-OAEP on ARMv7: the calls of the streaming hash functions

In the setting of the ARMv7 RSASSA-PSS proofs (`Proof/RsaPss/Arm/Base.lean`:
`Ctx L scr σ s`, a state of the body with our part of `scratch` at `scr`),
the streaming `init` (`init_vp`), `update` in its frame (`upd_vp`, of any
public range of bytes the body may read) and `finalize` in its frame
(`fin_vp`) of a hash function `G` (a `Pbkdf2.Stream.Arm.HashOK`), on the
state at `scratch + oSt` with the working space at `scratch + oW`: each
keeps any fact about memory (`Inv`) that its writes (the state, the
working space, the digest and the stack below the frame) do not reach, and
is constant time when its arguments are public.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa)
open VG.Impl.Pbkdf2.Stream.Arm (Hash)
open VG.Proof.Pbkdf2.Stream.Arm (HashOK count)
open VG.Proof.Rsa.Arm.Recover (VP)

theorem sSrc_lt : sSrc < 4096 := by decide
theorem sSrcLen_lt : sSrcLen < 4096 := by decide
theorem sDst_lt : sDst < 4096 := by decide
theorem sDstLen_lt : sDstLen < 4096 := by decide
theorem sRes_lt : sRes < 4096 := by decide
theorem sOk_lt : sOk < 4096 := by decide

theorem offsO : oEm = 0 ∧ oBuf = 1024 ∧ oSt = 3072 ∧ oDig = 3328 ∧ oLh = 3392 ∧ oCtr = 3456 ∧ oW = 3520 ∧
    oRsa = 8192 ∧ frameBytes = 128 ∧ sS = 64 ∧ sSrc = 68 ∧ sSrcLen = 72 ∧ sDst = 76 ∧ sDstLen = 80 ∧ sRes = 84 ∧
    sOk = 88 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `omega`, with the offsets of our part of `scratch` and of the frame as
numbers. -/
macro "oomega" : tactic => `(tactic| (obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := offsO; omega))

variable {L : Lay} {scr : BitVec 32}

/-- The bytes `[d, d + n)` the body may read, as one range. -/
theorem rbufCov {p : BitVec 32} {n : Nat} (hb : RBuf L p n) {σ s : State} (hs : L.St σ s) :
    Covers [⟨State.addr p, n⟩] (s.rd ++ s.wr) := by
  obtain ⟨R, hR, hc⟩ := hb.r
  refine Covers.one ⟨R, ?_, hc⟩
  rw [hs.rd, hs.wr, hs.ok.rd, hs.ok.wr]
  rcases List.mem_append.mp hR with hR | hR
  · exact List.mem_append_left _ (List.mem_append_left _ hR)
  · rcases List.mem_cons.mp hR with rfl | hR
    · exact List.mem_append_right _ List.mem_cons_self
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hR))

section
variable (hg : Geo L scr)
include hg

/-- A range of our part of `scratch` may be written, as one range. -/
theorem covS {σ s : State} (hs : L.St σ s) {o n : Nat} (ho : o < oRsa) (h : o + n ≤ oRsa) :
    Covers [⟨State.addr (scr + BitVec.ofNat 32 o), n⟩] s.wr := by
  rw [hg.addr ho]
  exact Covers.one (hg.wr hs h)

theorem fitS {o n : Nat} (h : o + n ≤ oRsa) : (scr + BitVec.ofNat 32 o).toNat + n ≤ 2 ^ 32 := by
  rw [hg.scr_lt (by omega)]; have := hg.fit; unfold oRsa at *; omega

/-- The stack below the frame and a range of our part of `scratch`. -/
theorem belowS {σ s : State} (hc : Ctx L scr σ s) {o n : Nat} (ho : o < oRsa) (h : o + n ≤ oRsa) :
    (Pbkdf2.Stream.Arm.below s).Disjoint ⟨State.addr (scr + BitVec.ofNat 32 o), n⟩ := by
  obtain ⟨σ', ok⟩ := hg.ok
  rw [hg.addr ho]
  exact (hg.low ok h).symm.sub_left (below_low hg hc)

theorem sp16 {σ s : State} (hc : Ctx L scr σ s) : 16 ≤ s.sp.toNat := by
  rw [hc.st.sp]; have := hg.C16; have := hc.st.ok.B56; omega

/-- A write to a range of our part of `scratch` and the stack below the
frame keeps `Ctx`. -/
theorem ctxW {σ s t : State} (hc : Ctx L scr σ s) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hs : ∀ r ∈ rs, (∃ o n, o + n ≤ oRsa ∧ r = sR scr o n) ∨ r = L.LOW)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.sp = s.sp) : Ctx L scr σ t := by
  obtain ⟨σ', ok⟩ := hg.ok
  refine hc.write hf (fun r hr => ?_) (fun r hr => ?_) rd wr sp
  · rcases hs r hr with ⟨o, n, h, rfl⟩ | rfl
    · exact hg.inW h
    · exact ⟨L.LOW, by simp [Lay.W], fun _ h => h⟩
  · rcases hs r hr with ⟨o, n, h, rfl⟩ | rfl
    · exact hg.slot ok h (by rw [hg.F]; decide)
    · exact Lay.fr_low (by decide) (by have := hc.st.ok.B56; have := L.B.isLt; omega)

end

/-! ## `init` -/

theorem init_vp (hg : Geo L scr) (G : Hash) (hG : HashOK G) {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame [sR scr oSt G.S, L.LOW] m m' → Inv σ m') :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem)
      (.seq (.block initArgs) (.call G.initN G.initC))
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ hG.SH.Repr s.mem (sa scr oSt) []) := by
  have hS := hG.hSB
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ s.gpr .r0 = scr + BitVec.ofNat 32 oSt)
    (VP.blk (by decide) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hi⟩ => ?_) ?_
  · prun [initArgs, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, Ctx.setReg_iff, hc, hi,
      movw_val (show oSt < 2 ^ 16 by decide)]
  have fitS : (scr + BitVec.ofNat 32 oSt).toNat + G.S ≤ 2 ^ 32 := fitS hg (by oomega)
  have cov : ∀ σ s, Ctx L scr σ s → Covers [⟨State.addr (scr + BitVec.ofNat 32 oSt), G.S⟩] s.wr :=
    fun σ s hc => covS hg hc.st (by oomega) (by oomega)
  refine VP.of_ct (fun _ _ => Pbkdf2.Stream.Arm.init_rel hG (st := scr + BitVec.ofNat 32 oSt)
    fun a b hab => ⟨hab.1.2.2, hab.2.2.2, fitS, cov _ _ hab.1.1, cov _ _ hab.2.1⟩) ?_
  rintro σ s ⟨hc, hi, r0⟩
  refine Pbkdf2.Stream.Arm.init_call hG r0 fitS (cov _ _ hc) fun s' af rp => ?_
  have aS : State.addr (scr + BitVec.ofNat 32 oSt) = sa scr oSt := hg.addr (by oomega)
  have fr : Frame [sR scr oSt G.S, L.LOW] s.mem s'.mem := by
    refine af.frame.sub fun r hr => ?_
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, by rw [aS]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, below_low hg hc⟩
  refine ⟨ctxW hg hc fr (fun r hr => ?_) af.rd af.wr af.sp, hI σ _ _ hi fr, by rw [← aS]; exact rp⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inl ⟨oSt, G.S, by oomega, rfl⟩
  · exact .inr rfl

/-! ## `update`, in its frame -/

/-- What `update`'s frame needs: the state, the data `[d, d + len)` (in
`r1`, `r7`), the working space (`r10`) and the count `c` (`r2:r3`). -/
structure UArgs (scr d : BitVec 32) (len c : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = scr + BitVec.ofNat 32 oSt
  r1 : s.gpr .r1 = d
  r7 : s.gpr .r7 = BitVec.ofNat 32 len
  r10 : s.gpr .r10 = scr + BitVec.ofNat 32 oW
  r2 : s.gpr .r2 = BitVec.ofNat 32 c
  r3 : s.gpr .r3 = 0

theorem count_of {s : State} {c : Nat} (hc : c < 2 ^ 32) (h2 : s.gpr .r2 = BitVec.ofNat 32 c) (h3 : s.gpr .r3 = 0) :
    count s = BitVec.ofNat 64 c := by
  simp only [count, h2, h3]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt (by omega)]
  simp

theorem upd_vp (hg : Geo L scr) (G : Hash) (hG : HashOK G) {d : BitVec 32} {len c : Nat}
    (hd : RBuf L d len) (dS : Region.Disjoint ⟨State.addr d, len⟩ (sR scr oSt G.S))
    (dW : Region.Disjoint ⟨State.addr d, len⟩ (sR scr oW hG.Wb)) (dL : Region.Disjoint ⟨State.addr d, len⟩ L.LOW)
    (hc32 : c < 2 ^ 32) {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame [sR scr oSt G.S, sR scr oW hG.Wb, L.LOW] m m' → Inv σ m')
    {msg dat : State → List Byte} :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ hG.SH.Repr s.mem (sa scr oSt) (msg σ) ∧ (msg σ).length = c ∧
        Spec.Sha256.bytesAt s.mem (State.addr d) len = dat σ ∧ UArgs scr d len c s)
      (updCall G)
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ hG.SH.Repr s.mem (sa scr oSt) (msg σ ++ dat σ)) := by
  have hS := hG.hSB
  have hWb : hG.Wb ≤ 512 := by have := hG.hWb; have := hG.hW; omega
  have aS : State.addr (scr + BitVec.ofNat 32 oSt) = sa scr oSt := hg.addr (by oomega)
  have aW : State.addr (scr + BitVec.ofNat 32 oW) = sa scr oW := hg.addr (by oomega)
  have sw : Region.Disjoint (sR scr oSt G.S) (sR scr oW hG.Wb) := Geo.sep (by oomega) (by oomega) (by oomega)
  have ua : ∀ σ s, Ctx L scr σ s → UArgs scr d len c s →
      Pbkdf2.Whole.Arm.UpdL hG s (scr + BitVec.ofNat 32 oSt) d (scr + BitVec.ofNat 32 oW) len := by
    intro σ s hc u
    refine ⟨u.r0, u.r1, u.r7, u.r10, hd.n32, sp16 hg hc, rbufCov hd hc.st,
      Covers.cons (covS hg hc.st (by oomega) (by oomega)) (covS hg hc.st (by oomega) (by oomega)), by rw [aS, aW]; exact sw,
      by rw [aS]; exact dS, by rw [aW]; exact dW, belowS hg hc (by oomega) (by oomega), dL.symm.sub_left (below_low hg hc),
      belowS hg hc (by oomega) (by oomega), fitS hg (by oomega), hd.fit, fitS hg (by oomega)⟩
  refine VP.of_ct (fun _ _ => Pbkdf2.Whole.Arm.upd_rel hG (sp := L.B) fun a b hab => ⟨ua _ _ hab.1.1 hab.1.2.2.2.2.2,
    ua _ _ hab.2.1 hab.2.2.2.2.2.2, by rw [count_of hc32 hab.1.2.2.2.2.2.r2 hab.1.2.2.2.2.2.r3,
      count_of hc32 hab.2.2.2.2.2.2.r2 hab.2.2.2.2.2.2.r3], hab.1.1.st.sp, hab.2.1.st.sp⟩) ?_
  rintro σ s ⟨hc, hi, rp, hl, hdat, u⟩
  refine Pbkdf2.Whole.Arm.upd_frame hG (ua σ s hc u) fun s' af hr => ?_
  have fr : Frame [sR scr oSt G.S, sR scr oW hG.Wb, L.LOW] s.mem s'.mem := by
    refine af.frame.sub fun r hr => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact ⟨_, List.mem_cons_self, by rw [aS]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by rw [aW]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), below_low hg hc⟩
  refine ⟨ctxW hg hc fr (fun r hr => ?_) af.rd af.wr af.sp, hI σ _ _ hi fr, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl ⟨oSt, G.S, by oomega, rfl⟩
    · exact .inl ⟨oW, hG.Wb, by oomega, rfl⟩
    · exact .inr rfl
  have := hr (msg σ) (by rw [aS]; exact rp) (by rw [count_of hc32 u.r2 u.r3, hl])
  rw [aS, hdat] at this
  exact this

/-! ## `finalize`, in its frame -/

/-- What `finalize`'s frame needs: the state, `out` at `scratch + o` (`r1`),
the working space (`r12`) and the count `c` (`r2:r3`). -/
structure FArgs (scr : BitVec 32) (o c : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = scr + BitVec.ofNat 32 oSt
  r1 : s.gpr .r1 = scr + BitVec.ofNat 32 o
  r12 : s.gpr .r12 = scr + BitVec.ofNat 32 oW
  r2 : s.gpr .r2 = BitVec.ofNat 32 c
  r3 : s.gpr .r3 = 0

theorem fin_vp (hg : Geo L scr) (G : Hash) (hG : HashOK G) {o c : Nat} (ho1 : o + G.F ≤ oSt ∨ oSt + G.S ≤ o)
    (ho2 : o + G.F ≤ oW ∨ oW + hG.Wb ≤ o) (hoR : o + G.F ≤ oRsa) (hc32 : c < 2 ^ 32) {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame [sR scr oSt G.S, sR scr o G.F, sR scr oW hG.Wb, L.LOW] m m' → Inv σ m')
    {msg : State → List Byte} :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ hG.SH.Repr s.mem (sa scr oSt) (msg σ) ∧ (msg σ).length = c ∧
        FArgs scr o c s)
      (finCall G)
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ (Spec.Sha256.bytesAt s.mem (sa scr o) G.F).take G.D = hG.SH.H.hash (msg σ)) := by
  have hS := hG.hSB
  have hF := hG.hF
  have hF0 : 0 < G.F := by have := hG.hD0; have := hG.hDF; omega
  have hWb : hG.Wb ≤ 512 := by have := hG.hWb; have := hG.hW; omega
  have aS : State.addr (scr + BitVec.ofNat 32 oSt) = sa scr oSt := hg.addr (by oomega)
  have aW : State.addr (scr + BitVec.ofNat 32 oW) = sa scr oW := hg.addr (by oomega)
  have aO : State.addr (scr + BitVec.ofNat 32 o) = sa scr o := hg.addr (by oomega)
  have fa : ∀ σ s, Ctx L scr σ s → FArgs scr o c s →
      Pbkdf2.Stream.Arm.FinArgs hG s (scr + BitVec.ofNat 32 oSt) (scr + BitVec.ofNat 32 o)
        (scr + BitVec.ofNat 32 oW) := by
    intro σ s hc f
    refine ⟨f.r0, f.r1, f.r12, sp16 hg hc,
      Covers.cons (covS hg hc.st (by oomega) (by oomega)) (Covers.cons (covS hg hc.st (by oomega) hoR) (covS hg hc.st (by oomega) (by oomega))),
      by rw [aS, aO]; exact Geo.sep (by omega) (by oomega) hoR, by rw [aS, aW]; exact Geo.sep (by oomega) (by oomega) (by oomega),
      by rw [aO, aW]; exact Geo.sep ho2 hoR (by oomega),
      belowS hg hc (by oomega) (by oomega), belowS hg hc (by oomega) hoR, belowS hg hc (by oomega) (by oomega), fitS hg (by oomega), fitS hg hoR,
      fitS hg (by oomega)⟩
  refine VP.of_ct (fun _ _ => Pbkdf2.Stream.Arm.fin_rel hG (sp := L.B) fun a b hab => ⟨fa _ _ hab.1.1 hab.1.2.2.2.2,
    fa _ _ hab.2.1 hab.2.2.2.2.2, by rw [count_of hc32 hab.1.2.2.2.2.r2 hab.1.2.2.2.2.r3,
      count_of hc32 hab.2.2.2.2.2.r2 hab.2.2.2.2.2.r3], hab.1.1.st.sp, hab.2.1.st.sp⟩) ?_
  rintro σ s ⟨hc, hi, rp, hl, f⟩
  refine Pbkdf2.Stream.Arm.fin_frame hG (fa σ s hc f) fun s' af hr => ?_
  have fr : Frame [sR scr oSt G.S, sR scr o G.F, sR scr oW hG.Wb, L.LOW] s.mem s'.mem := by
    refine af.frame.sub fun r hr => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact ⟨_, List.mem_cons_self, by rw [aS]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by rw [aO]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), by rw [aW]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
        below_low hg hc⟩
  refine ⟨ctxW hg hc fr (fun r hr => ?_) af.rd af.wr af.sp, hI σ _ _ hi fr, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact .inl ⟨oSt, G.S, by oomega, rfl⟩
    · exact .inl ⟨o, G.F, hoR, rfl⟩
    · exact .inl ⟨oW, hG.Wb, by oomega, rfl⟩
    · exact .inr rfl
  have := hr (msg σ) (by rw [aS]; exact rp) (by rw [hl]; omega) (by rw [count_of hc32 f.r2 f.r3, hl])
  rw [aO] at this
  exact this

/-! ## `r12 := r10` -/

theorem toR12_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r10]) (.block toR12) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem toR12_vp {F : State → State → Prop} (hF : ∀ σ s, F σ s → s.gpr .r10 = scr + BitVec.ofNat 32 oW)
    (hX : ∀ σ s v, F σ s → F σ (s.setReg .r12 v)) :
    VP F (.block toR12) (fun σ s => F σ s ∧ s.gpr .r12 = scr + BitVec.ofNat 32 oW) := by
  refine VP.taint _ toR12_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [hF _ _ h₁, hF _ _ h₂]
  · apply WP.of_runBlock
    simp only [toR12, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some]
    exact ⟨_, rfl, hX σ s _ hs, by rw [RegUpd.gpr_setReg]; simp [hF σ s hs]⟩

/-- An OR of two words is zero when both are. -/
theorem or_eq_zero32 (a b : BitVec 32) : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro e
    constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      have := congrArg (fun x => x.getLsbD i) e <;> simp_all
  · rintro ⟨rfl, rfl⟩; rfl

end VG.Proof.RsaOaep.Arm
