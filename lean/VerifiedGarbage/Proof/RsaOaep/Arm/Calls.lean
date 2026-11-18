module

public import VerifiedGarbage.Impl.RsaOaep.Arm
import VerifiedGarbage.Proof.RsaPss.Arm.CtXor
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
import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Bignum.Arm.ArrayFrame
import VerifiedGarbage.Proof.Bignum.Arm.Bases
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
import VerifiedGarbage.Proof.Bignum.Arm.MontCoreCT
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
import VerifiedGarbage.Proof.Bignum.Arm.MontInit
import VerifiedGarbage.Proof.Bignum.Arm.InverseArgs
import VerifiedGarbage.Proof.Bignum.Arm.InverseReady
import VerifiedGarbage.Proof.Bignum.Arm.KeepsBridge
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
import VerifiedGarbage.Proof.Bignum.Arm.LayoutExternal
import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
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
import VerifiedGarbage.Proof.Bignum.Arm.ProductArgs
import VerifiedGarbage.Proof.Bignum.Arm.ProductStage
import VerifiedGarbage.Proof.Bignum.Arm.R2
import VerifiedGarbage.Proof.Bignum.Arm.R2Constants
import VerifiedGarbage.Proof.Bignum.Arm.R2CountInit
import VerifiedGarbage.Proof.Bignum.Arm.R2Init
import VerifiedGarbage.Proof.Bignum.Arm.ReduceChoice
import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.RestoreSlots
import VerifiedGarbage.Proof.Bignum.Arm.ReverseByteStep
import VerifiedGarbage.Proof.Bignum.Arm.ReverseEncoding
import VerifiedGarbage.Proof.Bignum.Arm.ReverseRegion
import VerifiedGarbage.Proof.Bignum.Arm.Round
import VerifiedGarbage.Proof.Bignum.Arm.RoundFinishMemory
import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
import VerifiedGarbage.Proof.Bignum.Arm.Row
import VerifiedGarbage.Proof.Bignum.Arm.RowAdvance
import VerifiedGarbage.Proof.Bignum.Arm.RowFull
import VerifiedGarbage.Proof.Bignum.Arm.RowCarryMemory
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
import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeft
import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeftStep
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
import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import VerifiedGarbage.Proof.Bignum.Arm.Zero
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
public import VerifiedGarbage.Proof.Mgf1.Basic
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Pbkdf2.Memory
public import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
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
public import VerifiedGarbage.Proof.RsaPss.Arm.CtSel
import VerifiedGarbage.Proof.Sha256.StateMem
public meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtXor
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Upd
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Impl.Aes.Arm.Alloc
meta import VerifiedGarbage.Proof.AesGcm.Arm.Compare
meta import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.Arm.Entry
meta import VerifiedGarbage.Proof.AesGcm.Arm.Ghash1
meta import VerifiedGarbage.Proof.Bignum.Arm.ActivateWorkspace
meta import VerifiedGarbage.Proof.Bignum.Arm.AddCarry
meta import VerifiedGarbage.Proof.Bignum.Arm.StageCT
meta import VerifiedGarbage.Proof.Bignum.Arm.ArrayFrame
meta import VerifiedGarbage.Proof.Bignum.Arm.Bases
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
meta import VerifiedGarbage.Proof.Bignum.Arm.MontCoreCT
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
meta import VerifiedGarbage.Proof.Bignum.Arm.MontInit
meta import VerifiedGarbage.Proof.Bignum.Arm.InverseArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.InverseReady
meta import VerifiedGarbage.Proof.Bignum.Arm.KeepsBridge
meta import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
meta import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
meta import VerifiedGarbage.Proof.Bignum.Arm.LayoutExternal
meta import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
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
meta import VerifiedGarbage.Proof.Bignum.Arm.ProductArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.ProductStage
meta import VerifiedGarbage.Proof.Bignum.Arm.R2
meta import VerifiedGarbage.Proof.Bignum.Arm.R2Constants
meta import VerifiedGarbage.Proof.Bignum.Arm.R2CountInit
meta import VerifiedGarbage.Proof.Bignum.Arm.R2Init
meta import VerifiedGarbage.Proof.Bignum.Arm.ReduceChoice
meta import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
meta import VerifiedGarbage.Proof.Bignum.Arm.RestoreSlots
meta import VerifiedGarbage.Proof.Bignum.Arm.ReverseByteStep
meta import VerifiedGarbage.Proof.Bignum.Arm.ReverseEncoding
meta import VerifiedGarbage.Proof.Bignum.Arm.ReverseRegion
meta import VerifiedGarbage.Proof.Bignum.Arm.Round
meta import VerifiedGarbage.Proof.Bignum.Arm.RoundFinishMemory
meta import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
meta import VerifiedGarbage.Proof.Bignum.Arm.Row
meta import VerifiedGarbage.Proof.Bignum.Arm.RowAdvance
meta import VerifiedGarbage.Proof.Bignum.Arm.RowFull
meta import VerifiedGarbage.Proof.Bignum.Arm.RowCarryMemory
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
meta import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeft
meta import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeftStep
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
meta import VerifiedGarbage.Proof.Bignum.Arm.WideMul
meta import VerifiedGarbage.Proof.Bignum.Arm.Zero
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
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtSel
meta import VerifiedGarbage.Proof.Sha256.StateMem
public import VerifiedGarbage.Proof.RsaPss.Arm.Step
meta import VerifiedGarbage.Proof.RsaPss.Arm.Step
public import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Hash
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Hash
public import VerifiedGarbage.Proof.RsaPss.Arm.CtBase
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtBase
import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Impl.Bignum.Arm.Round
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
meta import VerifiedGarbage.Proof.Bignum.Arm.RoundState
meta import VerifiedGarbage.Impl.Bignum.Arm.Round
meta import VerifiedGarbage.Proof.Mont.Words32
meta import VerifiedGarbage.Proof.X25519.Arm.Instr
meta import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Aes.KeyExp

/-! ### `RsaPss.Arm.CtPad`, which this module and modules that import it used -/

section

/-! ### `RsaPss.Arm.CtLen`, which only this module used -/

section

/-!
# RSASSA-PSS on ARMv7: hashing, the block of the length field

`lenBlk_vp`: the block at `oLen` cleared, then the length field of `ℓ` (in
the slot `sL`) written at its end: its bytes are `lenBlk` of the length
field (`LB`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- The block at `oLen` holds zeros and the length field of `ℓ`. -/
def LB (scr : BitVec 32) (ℓ : Nat) (m : Mem) : Prop :=
  ∀ j < h.B, m (sa scr (oLen + j)) = lenBlk h.B h.L (h.md.lenBytes ℓ) j

theorem count0 {ℓ : Nat} (hℓ : ℓ < 2 ^ 32) : (0 : BitVec 32) ++ BitVec.ofNat 32 ℓ = BitVec.ofNat 64 ℓ := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hℓ,
    Nat.mod_eq_of_lt (by omega_arith)]
  simp

theorem lenBlk_vp (hg : Geo L scr) {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame [sR scr oLen h.B] m m' → Inv σ m') {ℓ : State → Nat}
    (hℓ : ∀ σ, ℓ σ < 2 ^ 32) :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ s.mem.readW (L.fr sL) 32 = BitVec.ofNat 32 (ℓ σ))
      (.seq (.block (lenClr h.sh)) (.seq Impl.Bignum.Arm.maskBytes (.seq (.block (lenArgs h.sh)) (.block h.H.len))))
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ LB h scr (ℓ σ) s.mem) := by
  have hN := h.N_le
  have hBl := h.B_le
  have hB64 := h.B_ge
  have hL := h.L_le
  have hNL := h.NL
  have fit := hg.fit
  have eN : h.H.md.N = h.N := rfl
  have eB : h.H.md.B = h.B := rfl
  have eL : h.H.md.L = h.L := rfl
  unfold oRsa at fit
  let I₁ : State → Mem → Prop := fun σ m => Inv σ m ∧ m.readW (L.fr sL) 32 = BitVec.ofNat 32 (ℓ σ)
  have hI₁ : ∀ σ m m', I₁ σ m → Frame [⟨State.addr (scr + BitVec.ofNat 32 oLen), h.B⟩] m m' → I₁ σ m' :=
    fun σ m m' ⟨hi, hs⟩ fr => by
      rw [hg.addr (by decide)] at fr
      obtain ⟨σ', ok⟩ := hg.ok
      exact ⟨hI σ _ _ hi fr, slot_keep fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hg.slot ok (by pomega) (by rw [hg.F]; decide)) hs⟩
  -- The block cleared.
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ I₁ σ s.mem ∧ s.gpr .r0 = scr + BitVec.ofNat 32 oLen ∧
      s.gpr .r2 = 0 ∧ s.gpr .lr = BitVec.ofNat 32 h.B)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hi, hs⟩ => ?_) ?_
  · prun [lenClr, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, Ctx.setReg_iff, hc, hi, hs,
      movw_val (show oLen < 2 ^ 16 by decide), movw_val (show h.B < 2 ^ 16 by omega_arith)]
    exact ⟨hi, hs⟩
  refine VP.seq (VP.mono (zero_vp (hg.wbuf (o := oLen) (n := h.B) (by pomega) (by omega_arith))
    (by omega_arith) hI₁) (fun _ _ h => h) fun _ _ h => h) ?_
  -- The length field.
  let I₂ : State → Mem → Prop := fun σ m => Inv σ m ∧ ∀ j < h.B - h.L, m (sa scr (oLen + j)) = 0
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ (Inv σ s.mem ∧ ∀ j < h.B, s.mem (sa scr (oLen + j)) = 0) ∧
      s.gpr .r0 = scr + BitVec.ofNat 32 (oLen - h.N) ∧ s.gpr .r4 = BitVec.ofNat 32 (ℓ σ) ∧ s.gpr .r5 = 0)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, ⟨hi, hs⟩, hz⟩ => ?_) ?_
  · have hz' : ∀ j < h.B, s.mem (sa scr (oLen + j)) = 0 := fun j hj => by
      rw [← hz j hj, hg.byteAt_scr (by pomega)]
    prun [lenArgs, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, Ctx.setReg_iff, hc, hi, hs,
      movw_val (show oLen - h.N < 2 ^ 16 by pomega), movw_val (show 0 < 2 ^ 16 by decide)]
    exact ⟨hz', rfl⟩
  refine VP.taint [.r0] h.lenCk (fun _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.1, h₂.2.2.1]) fun σ s ⟨hc, ⟨hi, hz⟩, r0, r4, r5⟩ => ?_
  have a0 : State.addr (s.gpr .r0) = sa scr (oLen - h.N) := by rw [r0, hg.addr (by pomega)]
  have e0 : State.addr (s.gpr .r0) + BitVec.ofNat 64 (h.N + (h.B - h.L)) = sa scr (oLen + (h.B - h.L)) := by
    rw [a0, sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    congr 2; unfold oLen; omega_arith
  refine WP.mono (h.len s (by rw [r0, hg.scr_lt (by pomega)]; pomega)
    (by rw [e0]; exact hg.wr hc.st (by pomega))) fun t ⟨g, rd, wr, sp, m⟩ => ?_
  rw [e0, r4, r5, count0 (hℓ σ), h.md.lenOf_eq _ (h.lenAll _ (hℓ σ))] at m
  have hlen := h.md.lenBytes_length (ℓ σ)
  have fr : Frame [sR scr (oLen + (h.B - h.L)) h.L] s.mem t.mem := by
    rw [m]
    refine (Frame.refl _ _).trans ?_
    intro a ha
    simp only [List.mem_singleton, forall_eq, Region.Contains, VG.WriteBytes.writeBytes, hlen] at ha ⊢
    rw [ite_eq_right (by omega_arith)]
  have hsub : Region.Sub (sR scr (oLen + (h.B - h.L)) h.L) (sR scr oLen h.B) :=
    Offset.sub _ (by omega_arith) (by omega_arith)
  have fr' : Frame [sR scr oLen h.B] s.mem t.mem := fr.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, hsub⟩
  obtain ⟨σ', ok⟩ := hg.ok
  refine ⟨hc.write fr' (fun r hr => ?_) (fun r hr => ?_) rd wr sp, hI σ _ _ hi fr', fun j hj => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by pomega)
  · simp only [List.mem_singleton] at hr; subst hr
    exact hg.slot ok (by pomega) (by rw [hg.F]; decide)
  · rw [m]
    simp only [VG.WriteBytes.writeBytes, lenBlk, hlen]
    have e : sa scr (oLen + j) - sa scr (oLen + (h.B - h.L)) = BitVec.ofNat 64 (2 ^ 64 - (h.B - h.L) + j) := by
      apply BitVec.eq_of_toNat_eq
      simp only [sa, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
      have := (State.addr scr).isLt
      pomega
    by_cases hj' : j < h.B - h.L
    · rw [ite_eq_left hj', ite_eq_right (by rw [e, BitVec.toNat_ofNat]; omega_arith), hz j hj]
    · rw [ite_eq_right hj', ite_eq_left (by rw [e, BitVec.toNat_ofNat]; omega_arith), e, BitVec.toNat_ofNat]
      congr 1; omega_arith

end VG.Proof.RsaPss.Arm

end

end

/-!
# RSASSA-PSS on ARMv7: hashing, the padding of a message of secret length

`pad_vp`: the padding loop leaves `padY` in `Y`'s `nbm` blocks: `0x80` in
byte `ℓ` and the block at `oLen` ORed into the last block of the padded
message, each through a mask computed without a branch (`eqBit`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

/-! ## Masks -/

/-- `((a ⊕ b) - 1) >> 31`: 1 if `a = b`, 0 otherwise, for `a, b < 2^31`. -/
theorem eqBit {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    ((BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b) - 1) >>> 31 = if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst h; rw [BitVec.xor_self, ite_eq_left rfl]; decide
  · rw [ite_eq_right h]
    have hx : (BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b).toNat < 2 ^ 31 := by
      rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
        Nat.mod_eq_of_lt (by omega_arith)]
      exact Nat.xor_lt_two_pow ha hb
    have hn : (BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b).toNat ≠ 0 := fun e => h (by
      have : BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b = 0#32 := BitVec.eq_of_toNat_eq (by simpa using e)
      have := BitVec.xor_eq_zero_iff.mp this
      have := congrArg BitVec.toNat this
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)] at this)
    generalize BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b = x at hx hn
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
    have h1 : (1 : BitVec 32).toNat = 1 := rfl
    rw [h1, show (2 ^ 32 - 1 + x.toNat) % 2 ^ 32 = x.toNat - 1 by omega_arith]
    show (x.toNat - 1) / 2 ^ 31 = 0
    exact Nat.div_eq_of_lt (by omega_arith)

/-- The byte the padding loop stores. -/
theorem padByte (b l : Byte) (c d : Prop) [Decidable c] [Decidable d] :
    ((b.setWidth 32 ||| (if c then (1 : BitVec 32) else 0) <<< 7) |||
        (l.setWidth 32 &&& (0 - if d then (1 : BitVec 32) else 0))).setWidth 8 =
      b ||| (if c then 0x80 else 0) ||| (if d then l else 0) := by
  have e1 : ∀ x : BitVec 8, (x.setWidth 32).setWidth 8 = x := fun x => by simp
  have e2 : ((1 : BitVec 32) <<< 7).setWidth 8 = 0x80 := by decide
  have e3 : ((0 : BitVec 32) <<< 7).setWidth 8 = 0 := by decide
  have e4 : ((0 : BitVec 32) - 1).setWidth 8 = BitVec.allOnes 8 := by decide
  have e5 : ((0 : BitVec 32) - 0).setWidth 8 = 0 := by decide
  by_cases hc : c <;> by_cases hd : d <;> simp only [hc, hd, BitVec.setWidth_or, BitVec.setWidth_and, e1, e2, e3, e4,
    e5, ite_true, ite_false, BitVec.and_allOnes] <;> simp

theorem ofNat_and_mask {k B : Nat} (hB : B = 64 ∨ B = 128) (hk : k < 2 ^ 32) :
    BitVec.ofNat 32 k &&& BitVec.ofNat 32 (B - 1) = BitVec.ofNat 32 (k % B) := by
  rcases hB with rfl | rfl
  · have := VG.Proof.MdStream.Arm.and_pow_sub_one (BitVec.ofNat 32 k) (n := 6) (by decide)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this; exact this
  · have := VG.Proof.MdStream.Arm.and_pow_sub_one (BitVec.ofNat 32 k) (n := 7) (by decide)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this; exact this

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-! ## The loop -/

/-- After `k` bytes of the padding loop. -/
structure PI (scr : BitVec 32) (T : Nat) (msg : List Byte) (k : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = scr + BitVec.ofNat 32 (oY + k)
  r1 : s.gpr .r1 = BitVec.ofNat 32 k
  lr : s.gpr .lr = BitVec.ofNat 32 (T - k)
  r4 : s.gpr .r4 = BitVec.ofNat 32 msg.length
  r5 : s.gpr .r5 = BitVec.ofNat 32 ((msg.length + h.L) / h.B)
  r6 : s.gpr .r6 = scr + BitVec.ofNat 32 oLen
  r7 : s.gpr .r7 = 0
  r9 : s.gpr .r9 = BitVec.ofNat 32 (h.B - 1)
  lb : LB h scr msg.length s.mem
  y : ∀ i < T, s.mem (sa scr (oY + i)) =
    if i < k then padY h.B h.L msg (h.md.lenBytes msg.length) i else msg.getD i 0

theorem padBody_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1, .lr, .r6, .r7, .r9])
    (.block (padBody h.sh)) hc).isSome = true := by
  rcases h.lg with ⟨e, -⟩ | ⟨e, -⟩ <;> simp only [padBody, e] <;> exact ⟨_, by taint_decide⟩

/-- One byte. -/
theorem padStep (hg : Geo L scr) {σ : State} {T : Nat} (hnb : T ≤ 2048) {msg : List Byte}
    (hfit : msg.length + 1 + h.L ≤ T) {k : Nat} (hk : k < T) {s : State}
    (hs : L.St σ s) (hp : PI h scr T msg k s) :
    WP isa (.block (padBody h.sh)) s fun t =>
      t.mem = s.mem.writeW (sa scr (oY + k)) (padY h.B h.L msg (h.md.lenBytes msg.length) k) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr .r0 = scr + BitVec.ofNat 32 (oY + (k + 1)) ∧
      t.gpr .r1 = BitVec.ofNat 32 (k + 1) ∧ t.gpr .lr = BitVec.ofNat 32 (T - (k + 1)) ∧
      t.gpr .r4 = s.gpr .r4 ∧ t.gpr .r5 = s.gpr .r5 ∧ t.gpr .r6 = s.gpr .r6 ∧ t.gpr .r7 = s.gpr .r7 ∧
      t.gpr .r9 = s.gpr .r9 ∧ t.z = decide (T - (k + 1) = 0) := by
  have hBl := h.B_le
  have hB64 := h.B_ge
  have hL := h.L_le
  have fit := hg.fit
  have hkB := Nat.mod_lt k (show 0 < h.B by omega_arith)
  have aY : State.addr (scr + BitVec.ofNat 32 (oY + k)) = sa scr (oY + k) := hg.addr (by pomega)
  have rY : InRegions (s.rd ++ s.wr) (sa scr (oY + k)) 1 := hg.rd hs (by pomega)
  have wY : InRegions s.wr (sa scr (oY + k)) 1 := hg.wr hs (by pomega)
  have e8 : (BitVec.ofNat 32 k &&& BitVec.ofNat 32 (h.B - 1)) + (scr + BitVec.ofNat 32 oLen) =
      scr + BitVec.ofNat 32 (oLen + k % h.B) := by
    rw [ofNat_and_mask h.B_cases (by pomega), BitVec.add_comm, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have aL8 : State.addr (scr + BitVec.ofNat 32 (oLen + k % h.B)) = sa scr (oLen + k % h.B) := hg.addr (by pomega)
  have rL8 : InRegions (s.rd ++ s.wr) (sa scr (oLen + k % h.B)) 1 := hg.rd hs (by pomega)
  have esh : BitVec.ofNat 32 k >>> lgB h.sh = BitVec.ofNat 32 (k / h.B) := by
    rw [VG.Proof.MdStream.Arm.ofNat_shr (by pomega), h.pow_lg]
  have eq1 := eqBit (a := k) (b := msg.length) (by pomega) (by pomega)
  have eq2 := eqBit (a := k / h.B) (b := (msg.length + h.L) / h.B) (by have := Nat.div_le_self k h.B; pomega)
    (by have := Nat.div_le_self (msg.length + h.L) h.B; pomega)
  have vY := hp.y k hk
  rw [ite_eq_right (Nat.lt_irrefl k)] at vY
  have vL := hp.lb (k % h.B) hkB
  have lr1 : BitVec.ofNat 32 (T - k) - 1 = BitVec.ofNat 32 (T - (k + 1)) := by
    rw [show T - k = (T - (k + 1)) + 1 by omega_arith]
    exact sub_one_ofNat (by omega_arith)
  prun [padBody, hp.r0, hp.r1, hp.r4, hp.r5, hp.r6, hp.r7, hp.r9, hp.lr, aY, rY, wY, e8, aL8, rL8, vY, vL,
    esh, eq1, eq2, lr1, padByte, h.lg_range, dpVal, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32, Nat.add_assoc]
  · exact VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32 k
  · rw [VG.Proof.X25519.Arm.ofNat_beq_zero (by omega_arith)]

/-- The padding loop: `padY` in `Y`'s `nbm` blocks. -/
theorem pad_vp (hg : Geo L scr) {nbm : Nat} (hnb : nbm * h.B ≤ 2048) (hnb0 : 0 < nbm) {msg : State → List Byte}
    (hfit : ∀ σ, (msg σ).length + 1 + h.L ≤ nbm * h.B) {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame [sR scr oY (nbm * h.B)] m m' → Inv σ m')
    (hsl : ∀ σ m, Inv σ m → m.readW (L.fr sL) 32 = BitVec.ofNat 32 (msg σ).length)
    (hsn : ∀ σ m, Inv σ m → m.readW (L.fr sNb) 32 = BitVec.ofNat 32 nbm) :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ LB h scr (msg σ).length s.mem ∧
        ∀ i < nbm * h.B, s.mem (sa scr (oY + i)) = (msg σ).getD i 0)
      (.seq (.block (padArgs h.sh)) (countLoop (padBody h.sh)))
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧
        ∀ i < nbm * h.B, s.mem (sa scr (oY + i)) = padY h.B h.L (msg σ) (h.md.lenBytes (msg σ).length) i) := by
  have hBl := h.B_le
  have hB64 := h.B_ge
  have hL := h.L_le
  have fit := hg.fit
  have hpos : 0 < nbm * h.B := Nat.mul_pos hnb0 (by omega_arith)
  generalize hT : nbm * h.B = T at hnb hpos hfit hI ⊢
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ PI h scr T (msg σ) 0 s)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hi, lb, hy⟩ => ?_) ?_
  · have esh : (BitVec.ofNat 32 (msg σ).length + BitVec.ofNat 32 h.L) >>> lgB h.sh =
        BitVec.ofNat 32 (((msg σ).length + h.L) / h.B) := by
      rw [BitVec.ofNat_add_ofNat, VG.Proof.MdStream.Arm.ofNat_shr (by have := hfit σ; pomega), h.pow_lg]
    have esl : BitVec.ofNat 32 nbm <<< lgB h.sh = BitVec.ofNat 32 T := by
      rw [← hT]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, h.pow_lg,
        Nat.mod_eq_of_lt (a := nbm) (by have : nbm ≤ T := hT ▸ Nat.le_mul_of_pos_right nbm (show 0 < h.B by omega_arith); omega_arith)]
    prun [padArgs, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, Ctx.setReg_iff, hc, hi,
      hsl σ _ hi, hsn σ _ hi, movw_val (show oY < 2 ^ 16 by decide), movw_val (show oLen < 2 ^ 16 by decide),
      movw_val (show h.L < 2 ^ 16 by omega_arith), movw_val (show h.B - 1 < 2 ^ 16 by omega_arith),
      movw_val (show 0 < 2 ^ 16 by decide), esh, esl, h.lg_range, dpVal]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, lb, fun i hi' =>
      (hy i hi').trans (ite_eq_right (Nat.not_lt_zero i)).symm⟩
  let I : Nat → State → State → Prop := fun n σ s =>
    n ≤ T ∧ Ctx L scr σ s ∧ Inv σ s.mem ∧ PI h scr T (msg σ) (T - n) s
  refine (VP.loop (I := I) (fun n => ?_) (T - 1)).mono (fun σ s ⟨hc, hi, hp⟩ => ⟨by omega_arith, hc, hi,
    by rw [show T - (T - 1 + 1) = 0 by omega_arith]; exact hp⟩) fun _ _ h => h
  refine VP.taint _ (padBody_taint h) (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hn, hc, hi, hp⟩ => ?_
  · obtain ⟨-, -, -, p₁⟩ := h₁
    obtain ⟨-, -, -, p₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [p₁.r0, p₂.r0]
    · rw [p₁.r1, p₂.r1]
    · rw [p₁.lr, p₂.lr]
    · rw [p₁.r6, p₂.r6]
    · rw [p₁.r7, p₂.r7]
    · rw [p₁.r9, p₂.r9]
  generalize hk : T - (n + 1) = k at hp
  have hkn : k < T := by omega_arith
  refine WP.mono (padStep h hg hnb (hfit σ) hkn hc.st hp)
    fun t ⟨m, rd, wr, sp, r0, r1, lr, r4, r5, r6, r7, r9, z⟩ => ?_
  have fr : Frame [sR scr oY T] s.mem t.mem := by
    rw [m]; exact frame_byte scr _ _ (by omega_arith) (by omega_arith) (by pomega)
  obtain ⟨σ', ok⟩ := hg.ok
  have hc' : Ctx L scr σ t := hc.write fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by pomega))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by pomega) (by rw [hg.F]; decide))
    rd wr sp
  have pk : PI h scr T (msg σ) (k + 1) t := by
    refine ⟨r0, r1, lr, r4.trans hp.r4, r5.trans hp.r5, r6.trans hp.r6, r7.trans hp.r7, r9.trans hp.r9,
      fun j hj => ?_, fun i hi' => ?_⟩
    · rw [m, sa_write scr _ _ (by pomega) (by pomega), ite_eq_right (by have := hp.lb; pomega)]
      exact hp.lb j hj
    · rw [m, sa_write scr _ _ (by pomega) (by pomega), hp.y i hi']
      by_cases e : i = k
      · subst e; rw [ite_eq_left rfl, ite_eq_left (Nat.lt_succ_self _)]
      · rw [ite_eq_right (by omega_arith)]
        by_cases e' : i < k
        · rw [ite_eq_left e', ite_eq_left (by omega_arith)]
        · rw [ite_eq_right e', ite_eq_right (by omega_arith)]
  refine ⟨by
    rw [VG.Proof.X25519.Arm.eval_ne, z, show T - (k + 1) = n by omega_arith]
    cases n <;> simp, fun h0 => ⟨hc', hI σ _ _ hi fr, fun i hi' => ?_⟩,
    fun hpos' => ⟨by omega_arith, hc', hI σ _ _ hi fr, by rw [show T - n = k + 1 by omega_arith]; exact pk⟩⟩
  rw [pk.y i hi', ite_eq_left (by omega_arith)]

end VG.Proof.RsaPss.Arm

end

end

/-! ### `RsaPss.Arm.CtMgf`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS and RSAES-OAEP on ARMv7: facts for MGF1 and the slots

What MGF1's proofs (`Proof/RsaOaep/Arm/Mgf.lean`) need of the slots, of
the counter's bytes and of the hash function (`PssHash.valid`), and the
stack of a streaming function's frame (`below_low`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.MdStream (Md)

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- The hash function as MGF1 takes it has digests of `hLen` bytes. -/
theorem PssHash.valid : Proof.Mgf1.Valid h.G := by
  refine ⟨by rw [h.glen]; exact h.D_pos, fun x => ?_⟩
  rw [h.hash, h.ok.hash, List.length_take, Md.hash, h.md.digest_length, h.glen]
  exact Nat.min_eq_left h.D_le


/-- A slot is in what the body may write. -/
theorem slotW (hg : Geo L scr) {d : Nat} (hd : d + 4 ≤ frameBytes) : ∃ R ∈ L.W, Region.Sub (slotR L d) R :=
  ⟨L.FR, List.mem_cons_self, Offset.sub_base _ (by rw [hg.F]; exact hd)⟩


/-- Two slots apart. -/
theorem slotSep {d e : Nat} (hd : d + 4 ≤ frameBytes) (he : e + 4 ≤ frameBytes) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (slotR L d).Disjoint (slotR L e) :=
  Lay.fr_sep h (by unfold frameBytes at hd; omega_using [hd]) (by unfold frameBytes at he; omega_using [he])


/-- A word's bits as a mask. -/
theorem selW (a b : BitVec 32) (c : Prop) [Decidable c] : b ^^^ ((a ^^^ b) &&& maskOf c) = if c then a else b := by
  by_cases hc : c
  · simp only [maskOf, hc, ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm a b, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · simp [maskOf, hc]


/-- The counter's bytes. -/
theorem i2osp4_getD (c j : Nat) (hj : j < 4) :
    (Spec.Rsa.i2osp c 4).getD j 0 = BitVec.ofNat 8 (c / 256 ^ (3 - j)) := by
  simp [Spec.Rsa.i2osp, List.getD_eq_getElem?_getD, hj]


theorem i2osp4_length (c : Nat) : (Spec.Rsa.i2osp c 4).length = 4 := by simp [Spec.Rsa.i2osp]


/-- A slot read after a write of another. -/
theorem slot_ww (m : Mem) {d e : Nat} (v : BitVec 32) (hd : d + 4 ≤ frameBytes) (he : e + 4 ≤ frameBytes)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) : (m.writeW (L.fr e) v).readW (L.fr d) 32 = m.readW (L.fr d) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by unfold frameBytes at hd; omega_using [hd]) (by unfold frameBytes at he; omega_using [he]))
    (by decide)


theorem ctrPut_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1])
    (.block ctrPut) hc).isSome = true := ⟨_, by taint_decide⟩


theorem shr0 (c : Nat) : (BitVec.ofNat 32 c).setWidth 8 = BitVec.ofNat 8 (c / 256 ^ 0) := by
  rw [Nat.pow_zero, Nat.div_one]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_using []


theorem bit_z (p : Prop) [Decidable p] : ((if p then (1 : BitVec 32) else 0) - 0 == 0) = decide (¬ p) := by
  by_cases hp : p <;> simp [hp]


/-- The 16 bytes below the stack pointer, where a streaming function's frame
goes, are in our callees' stack. -/
theorem below_low (hg : Geo L scr) {σ s : State} (hc : Ctx L scr σ s) :
    Region.Sub (Pbkdf2.Stream.Arm.below s) L.LOW := by
  have hC := hg.C16
  have hB := hc.st.ok.B56
  rw [Pbkdf2.Stream.Arm.below, hc.st.sp]
  show Region.Sub ⟨State.addr L.B - BitVec.ofNat 64 16, 16⟩ ⟨State.addr L.B - BitVec.ofNat 64 L.C, L.C⟩
  exact Offset.sub_below _ hC (by omega_using [hC])

end VG.Proof.RsaPss.Arm

end

end

/-!
# RSAES-OAEP on ARMv7: the calls of the streaming hash functions

In the setting of the ARMv7 RSASSA-PSS proofs (`Proof/RsaPss/Arm/Step.lean`:
`Ctx L scr σ s`, a state of the body with our part of `scratch` at `scr`),
the streaming `init` (`initArgs_vp`, `initCall_vp`), `update` in its frame (`upd_vp`, of any
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
theorem sTab_lt : sTab < 4096 := by decide
theorem sHl_lt : sHl < 4096 := by decide

theorem offsO : oEm = 0 ∧ oBuf = 1024 ∧ oSt = 3072 ∧ oDig = 3328 ∧ oLh = 3392 ∧ oCtr = 3456 ∧ oW = 3520 ∧
    oRsa = 8192 ∧ frameBytes = 128 ∧ sS = 64 ∧ sSrc = 68 ∧ sSrcLen = 72 ∧ sDst = 76 ∧ sDstLen = 80 ∧ sRes = 84 ∧
    sOk = 88 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `omega`, with the offsets of our part of `scratch` and of the frame as
numbers. -/
macro "oomega" : tactic => `(tactic| (obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := offsO; omega_arith))

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
  rw [hg.scr_lt (by omega_arith)]; have := hg.fit; unfold oRsa at *; omega_arith

/-- The stack below the frame and a range of our part of `scratch`. -/
theorem belowS {σ s : State} (hc : Ctx L scr σ s) {o n : Nat} (ho : o < oRsa) (h : o + n ≤ oRsa) :
    (Pbkdf2.Stream.Arm.below s).Disjoint ⟨State.addr (scr + BitVec.ofNat 32 o), n⟩ := by
  obtain ⟨σ', ok⟩ := hg.ok
  rw [hg.addr ho]
  exact (hg.low ok h).symm.sub_left (below_low hg hc)

theorem sp16 {σ s : State} (hc : Ctx L scr σ s) : 16 ≤ s.sp.toNat := by
  rw [hc.st.sp]; have := hg.C16; have := hc.st.ok.B56; omega_arith

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
    · exact Lay.fr_low (by decide) (by have := hc.st.ok.B56; have := L.B.isLt; omega_arith)

end

/-! ## `init` -/

/-- `init`'s argument, the state. -/
theorem initArgs_vp (hg : Geo L scr) {Inv : State → Mem → Prop} :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem) (.block initArgs)
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ s.gpr .r0 = scr + BitVec.ofNat 32 oSt) := by
  refine VP.blk (by decide) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hi⟩ => ?_
  prun [initArgs, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, Ctx.setReg_iff, hc, hi,
    movw_val (show oSt < 2 ^ 16 by decide)]

/-- The call of `init`. -/
theorem initCall_vp (hg : Geo L scr) (G : Hash) (hG : HashOK G) {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame [sR scr oSt G.S, L.LOW] m m' → Inv σ m') :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ s.gpr .r0 = scr + BitVec.ofNat 32 oSt)
      (.call G.initN G.initC)
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ hG.SH.Repr s.mem (sa scr oSt) []) := by
  have hS := hG.hSB
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
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt (by omega_arith)]
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
  have hWb : hG.Wb ≤ 512 := by have := hG.hWb; have := hG.hW; omega_arith
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
  have hF0 : 0 < G.F := by have := hG.hD0; have := hG.hDF; omega_arith
  have hWb : hG.Wb ≤ 512 := by have := hG.hWb; have := hG.hW; omega_arith
  have aS : State.addr (scr + BitVec.ofNat 32 oSt) = sa scr oSt := hg.addr (by oomega)
  have aW : State.addr (scr + BitVec.ofNat 32 oW) = sa scr oW := hg.addr (by oomega)
  have aO : State.addr (scr + BitVec.ofNat 32 o) = sa scr o := hg.addr (by oomega)
  have fa : ∀ σ s, Ctx L scr σ s → FArgs scr o c s →
      Pbkdf2.Stream.Arm.FinArgs hG s (scr + BitVec.ofNat 32 oSt) (scr + BitVec.ofNat 32 o)
        (scr + BitVec.ofNat 32 oW) := by
    intro σ s hc f
    refine ⟨f.r0, f.r1, f.r12, sp16 hg hc,
      Covers.cons (covS hg hc.st (by oomega) (by oomega)) (Covers.cons (covS hg hc.st (by oomega) hoR) (covS hg hc.st (by oomega) (by oomega))),
      by rw [aS, aO]; exact Geo.sep (by omega_arith) (by oomega) hoR, by rw [aS, aW]; exact Geo.sep (by oomega) (by oomega) (by oomega),
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
  have := hr (msg σ) (by rw [aS]; exact rp) (by rw [hl]; omega_arith) (by rw [count_of hc32 f.r2 f.r3, hl])
  rw [aO] at this
  exact this

/-! ## The table's words -/

/-- The load of the table's word `k`, through `r4`, its address. -/
theorem tword_cert {k : Nat} (hk : k < 3) :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4]) (.block [.ldr .r4 .r4 (4 * k)]) hc).isSome = true := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega_using [hk]) with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- The load of the table's digest length (its word 4), through `r0`, to its slot. -/
theorem tabD_cert :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r12]) (.block [.ldr .r0 .r0 24, st .r0 sHl]) hc).isSome =
      true := ⟨_, by taint_decide⟩

/-- The load of a table's digest length (its word 4), through `r1`. -/
theorem lenWord_cert :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r1]) (.block [.ldr .r1 .r1 24]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- The comparisons of the digest length in `r1` with each of `lens`. -/
theorem lens_certs : ∀ x ∈ Impl.RsaOaep.Arm.lens, x < 2 ^ 32 ∧ encodable (BitVec.ofNat 32 x) = true ∧
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs []) (.block [.cmp .r1 (.imm (BitVec.ofNat 32 x))]) hc).isSome =
      true := by
  intro x hx
  simp only [Impl.RsaOaep.Arm.lens, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide, _, by taint_decide⟩

theorem UArgs.r4 {d : BitVec 32} {len c : Nat} {s : State} (h : UArgs scr d len c s) (v : BitVec 32) :
    UArgs scr d len c (s.setReg .r4 v) := by
  obtain ⟨a, b, e, f, g, i⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [VG.Arm.RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte] <;>
    with_reducible assumption

theorem FArgs.r4 {o c : Nat} {s : State} (h : FArgs scr o c s) (v : BitVec 32) :
    FArgs scr o c (s.setReg .r4 v) := by
  obtain ⟨a, b, e, f, g⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [VG.Arm.RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte] <;>
    with_reducible assumption

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
