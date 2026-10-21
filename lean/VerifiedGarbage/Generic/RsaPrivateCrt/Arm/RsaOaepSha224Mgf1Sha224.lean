module

public import VerifiedGarbage.Spec.Mgf1

public import VerifiedGarbage.TCB.Artifact

public import VerifiedGarbage.TCB.Arm.Target

public import VerifiedGarbage.Spec.RsaOaep.Precomputed

public import Init.Data.String.Defs


public import VerifiedGarbage.Proof.Rsa.Arm.PrivImpl
public import VerifiedGarbage.Proof.RsaOaep.Arm.Mgf
public import VerifiedGarbage.Proof.Rsa.Arm.PublicOfCrt
public import VerifiedGarbage.Proof.RsaOaep.Arm.EncVerified
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha224
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.RsaOaep.Arm.EncSat
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticExternal
public import VerifiedGarbage.Proof.Bignum.Arm.ArrayCompare
public import VerifiedGarbage.Proof.Bignum.Arm.ArrayCompareArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ArrayCompareCT
public import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWide
public import VerifiedGarbage.Proof.Bignum.Arm.ClearOperandBuffer
public import VerifiedGarbage.Proof.Bignum.Arm.ClearOperandBufferArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpBit
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpBitsCT
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpByte
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpByteHead
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpByteHeadCT
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpByteNext
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpByteSave
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpBytes
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpBytesCT
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpInit
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpPhase
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpPhaseCT
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpRound
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpRoundCT
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpStep
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpStepCT
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopCT
public import VerifiedGarbage.Proof.Bignum.Arm.ExpBitTest
public import VerifiedGarbage.Proof.Bignum.Arm.ExpByteLoad
public import VerifiedGarbage.Proof.Bignum.Arm.ExpControl
public import VerifiedGarbage.Proof.Bignum.Arm.ExpControls
public import VerifiedGarbage.Proof.Bignum.Arm.ExpControlsCT
public import VerifiedGarbage.Proof.Bignum.Arm.ExpInit
public import VerifiedGarbage.Proof.Bignum.Arm.ExpInitCT
public import VerifiedGarbage.Proof.Bignum.Arm.ExponentAccumulate
public import VerifiedGarbage.Proof.Bignum.Arm.ExponentByte
public import VerifiedGarbage.Proof.Bignum.Arm.ExponentCheck
public import VerifiedGarbage.Proof.Bignum.Arm.ExponentCheckCT
public import VerifiedGarbage.Proof.Bignum.Arm.ExponentCheckMath
public import VerifiedGarbage.Proof.Bignum.Arm.ExponentFlag
public import VerifiedGarbage.Proof.Bignum.Arm.ExponentSaturate
public import VerifiedGarbage.Proof.Bignum.Arm.ExponentTest
public import VerifiedGarbage.Proof.Bignum.Arm.ExponentTests
public import VerifiedGarbage.Proof.Bignum.Arm.ExponentWords
public import VerifiedGarbage.Proof.Bignum.Arm.ExportBE
public import VerifiedGarbage.Proof.Bignum.Arm.ExportBEArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ExportBECT
public import VerifiedGarbage.Proof.Bignum.Arm.ExportMasked
public import VerifiedGarbage.Proof.Bignum.Arm.HeaderStore
public import VerifiedGarbage.Proof.Bignum.Arm.ImportArray
public import VerifiedGarbage.Proof.Bignum.Arm.ImportArrayCT
public import VerifiedGarbage.Proof.Bignum.Arm.ImportArrayLayout
public import VerifiedGarbage.Proof.Bignum.Arm.ImportArraySwap
public import VerifiedGarbage.Proof.Bignum.Arm.ImportOperand
public import VerifiedGarbage.Proof.Bignum.Arm.ImportOperandCT
public import VerifiedGarbage.Proof.Bignum.Arm.InitInverseCT
public import VerifiedGarbage.Proof.Bignum.Arm.InputCompare
public import VerifiedGarbage.Proof.Bignum.Arm.InputCompareArgs
public import VerifiedGarbage.Proof.Bignum.Arm.InputCompareCT
public import VerifiedGarbage.Proof.Bignum.Arm.LoadBECT
public import VerifiedGarbage.Proof.Bignum.Arm.LoadBEFnCT
public import VerifiedGarbage.Proof.Bignum.Arm.MergeAcceptance
public import VerifiedGarbage.Proof.Bignum.Arm.MergeAcceptanceCT
public import VerifiedGarbage.Proof.Bignum.Arm.MergeAcceptanceLayout
public import VerifiedGarbage.Proof.Bignum.Arm.MontOp
public import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
public import VerifiedGarbage.Proof.Bignum.Arm.PcPrepare
public import VerifiedGarbage.Proof.Bignum.Arm.PdAccept
public import VerifiedGarbage.Proof.Bignum.Arm.PdAcceptCT
public import VerifiedGarbage.Proof.Bignum.Arm.PdAccepted
public import VerifiedGarbage.Proof.Bignum.Arm.PdApply
public import VerifiedGarbage.Proof.Bignum.Arm.PdApplyCT
public import VerifiedGarbage.Proof.Bignum.Arm.PdBody
public import VerifiedGarbage.Proof.Bignum.Arm.PdBodyCT
public import VerifiedGarbage.Proof.Bignum.Arm.PdCheckFirst
public import VerifiedGarbage.Proof.Bignum.Arm.PdCheckedCT
public import VerifiedGarbage.Proof.Bignum.Arm.PdChecks
public import VerifiedGarbage.Proof.Bignum.Arm.PdChecksCT
public import VerifiedGarbage.Proof.Bignum.Arm.PdContract
public import VerifiedGarbage.Proof.Bignum.Arm.PdContractInput
public import VerifiedGarbage.Proof.Bignum.Arm.PdControls
public import VerifiedGarbage.Proof.Bignum.Arm.PdControlsCT
public import VerifiedGarbage.Proof.Bignum.Arm.PdEntry
public import VerifiedGarbage.Proof.Bignum.Arm.PdEntryCT
public import VerifiedGarbage.Proof.Bignum.Arm.PdEntryMemory
public import VerifiedGarbage.Proof.Bignum.Arm.PdEntryReady
public import VerifiedGarbage.Proof.Bignum.Arm.PdFail
public import VerifiedGarbage.Proof.Bignum.Arm.PdFailCT
public import VerifiedGarbage.Proof.Bignum.Arm.PdFinish
public import VerifiedGarbage.Proof.Bignum.Arm.PdFinishCT
public import VerifiedGarbage.Proof.Bignum.Arm.PdFn
public import VerifiedGarbage.Proof.Bignum.Arm.PdFnCT
public import VerifiedGarbage.Proof.Bignum.Arm.PdImportCT
public import VerifiedGarbage.Proof.Bignum.Arm.PdImported
public import VerifiedGarbage.Proof.Bignum.Arm.PdImportedCT
public import VerifiedGarbage.Proof.Bignum.Arm.PdInputImport
public import VerifiedGarbage.Proof.Bignum.Arm.PdInputImportCT
public import VerifiedGarbage.Proof.Bignum.Arm.PdInverse
public import VerifiedGarbage.Proof.Bignum.Arm.PdOdd
public import VerifiedGarbage.Proof.Bignum.Arm.PdOddCT
public import VerifiedGarbage.Proof.Bignum.Arm.PdOddFinish
public import VerifiedGarbage.Proof.Bignum.Arm.PdOddRead
public import VerifiedGarbage.Proof.Bignum.Arm.PdParity
public import VerifiedGarbage.Proof.Bignum.Arm.PdPrepare
public import VerifiedGarbage.Proof.Bignum.Arm.PdPrepareCT
public import VerifiedGarbage.Proof.Bignum.Arm.PdPush
public import VerifiedGarbage.Proof.Bignum.Arm.PdWritten
public import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
public import VerifiedGarbage.Proof.Bignum.Arm.PublicAccepted
public import VerifiedGarbage.Proof.Bignum.Arm.PublicArgs
public import VerifiedGarbage.Proof.Bignum.Arm.PublicArgsCT
public import VerifiedGarbage.Proof.Bignum.Arm.PublicEntry
public import VerifiedGarbage.Proof.Bignum.Arm.PublicEntryReady
public import VerifiedGarbage.Proof.Bignum.Arm.PublicFail
public import VerifiedGarbage.Proof.Bignum.Arm.PublicPush
public import VerifiedGarbage.Proof.Bignum.Arm.PublicSaved
public import VerifiedGarbage.Proof.Bignum.Arm.PublicStackFrame
public import VerifiedGarbage.Proof.Bignum.Arm.PublicWritten
public import VerifiedGarbage.Proof.Bignum.Arm.R2CT
public import VerifiedGarbage.Proof.Bignum.Arm.ReadPrefix
public import VerifiedGarbage.Proof.Bignum.Arm.ReverseBuffer
public import VerifiedGarbage.Proof.Bignum.Arm.ReverseBytesCT
public import VerifiedGarbage.Proof.Bignum.Arm.RowLoopCT
public import VerifiedGarbage.Proof.Bignum.Arm.SaveAcceptance
public import VerifiedGarbage.Proof.Bignum.Arm.SaveAcceptanceCT
public import VerifiedGarbage.Proof.Bignum.Arm.SaveAcceptanceLayout
public import VerifiedGarbage.Proof.Bignum.Arm.SetupCT
public import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeftCT
public import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
public import VerifiedGarbage.Proof.Bignum.Arm.SquareOpCT
public import VerifiedGarbage.Proof.Bignum.Arm.StoreBE
public import VerifiedGarbage.Proof.Bignum.Arm.SubCompare
public import VerifiedGarbage.Proof.Bignum.Arm.SubRowCT
public import VerifiedGarbage.Proof.Bignum.FoldedPublic
public import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
public import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Instances
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Calls
public import VerifiedGarbage.Proof.Rsa.Arm.PrivContract
public import VerifiedGarbage.Proof.Rsa.Arm.PrivContractInput
public import VerifiedGarbage.Proof.Rsa.Arm.PrivEntryReady
public import VerifiedGarbage.Proof.Rsa.Arm.PrivFn
public import VerifiedGarbage.Proof.Rsa.Arm.PrivFnCT
public import VerifiedGarbage.Proof.Rsa.Arm.PrivVerified
public import VerifiedGarbage.Proof.RsaOaep.Arm.Label
public import VerifiedGarbage.Proof.RsaPss.Arm.YDig
public import VerifiedGarbage.Proof.RsaPss.Params
public import VerifiedGarbage.Proof.RsaPss.SignCases
public import VerifiedGarbage.Proof.RsaOaep.Arm.DecVerified
import VerifiedGarbage.Proof.RsaOaep.Arm.DecSat
public import VerifiedGarbage.Proof.RsaOaep.Arm.DecSat
public import VerifiedGarbage.Proof.RsaOaep.Arm.DecEnd
public import VerifiedGarbage.Proof.RsaOaep.Arm.DecFail
public import VerifiedGarbage.Proof.RsaOaep.Arm.DecSpec
public import VerifiedGarbage.Proof.RsaPss.Arm.VfPass
public import VerifiedGarbage.Proof.RsaPss.Arm.VfShift
public import VerifiedGarbage.Proof.RsaPss.Arm.VfY
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticExternal
import VerifiedGarbage.Proof.Bignum.Arm.ArrayCompare
import VerifiedGarbage.Proof.Bignum.Arm.ArrayCompareArgs
import VerifiedGarbage.Proof.Bignum.Arm.ArrayCompareCT
import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWide
import VerifiedGarbage.Proof.Bignum.Arm.ClearOperandBuffer
import VerifiedGarbage.Proof.Bignum.Arm.ClearOperandBufferArgs
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
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopCT
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
import VerifiedGarbage.Proof.Bignum.Arm.ExportBE
import VerifiedGarbage.Proof.Bignum.Arm.ExportBEArgs
import VerifiedGarbage.Proof.Bignum.Arm.ExportBECT
import VerifiedGarbage.Proof.Bignum.Arm.ExportMasked
import VerifiedGarbage.Proof.Bignum.Arm.HeaderStore
import VerifiedGarbage.Proof.Bignum.Arm.ImportArray
import VerifiedGarbage.Proof.Bignum.Arm.ImportArrayCT
import VerifiedGarbage.Proof.Bignum.Arm.ImportArrayLayout
import VerifiedGarbage.Proof.Bignum.Arm.ImportArraySwap
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperand
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperandCT
import VerifiedGarbage.Proof.Bignum.Arm.InitInverseCT
import VerifiedGarbage.Proof.Bignum.Arm.InputCompare
import VerifiedGarbage.Proof.Bignum.Arm.InputCompareArgs
import VerifiedGarbage.Proof.Bignum.Arm.InputCompareCT
import VerifiedGarbage.Proof.Bignum.Arm.LoadBECT
import VerifiedGarbage.Proof.Bignum.Arm.LoadBEFnCT
import VerifiedGarbage.Proof.Bignum.Arm.MergeAcceptance
import VerifiedGarbage.Proof.Bignum.Arm.MergeAcceptanceCT
import VerifiedGarbage.Proof.Bignum.Arm.MergeAcceptanceLayout
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
import VerifiedGarbage.Proof.Bignum.Arm.PcPrepare
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
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
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
import VerifiedGarbage.Proof.Bignum.Arm.R2CT
import VerifiedGarbage.Proof.Bignum.Arm.ReadPrefix
import VerifiedGarbage.Proof.Bignum.Arm.ReverseBuffer
import VerifiedGarbage.Proof.Bignum.Arm.ReverseBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.RowLoopCT
import VerifiedGarbage.Proof.Bignum.Arm.SaveAcceptance
import VerifiedGarbage.Proof.Bignum.Arm.SaveAcceptanceCT
import VerifiedGarbage.Proof.Bignum.Arm.SaveAcceptanceLayout
import VerifiedGarbage.Proof.Bignum.Arm.SetupCT
import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeftCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.SquareOpCT
import VerifiedGarbage.Proof.Bignum.Arm.StoreBE
import VerifiedGarbage.Proof.Bignum.Arm.SubCompare
import VerifiedGarbage.Proof.Bignum.Arm.SubRowCT
import VerifiedGarbage.Proof.Bignum.FoldedPublic
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Instances
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Calls
import VerifiedGarbage.Proof.Rsa.Arm.PrivContract
import VerifiedGarbage.Proof.Rsa.Arm.PrivContractInput
import VerifiedGarbage.Proof.Rsa.Arm.PrivEntryReady
import VerifiedGarbage.Proof.Rsa.Arm.PrivFn
import VerifiedGarbage.Proof.Rsa.Arm.PrivFnCT
import VerifiedGarbage.Proof.Rsa.Arm.PrivVerified
import VerifiedGarbage.Proof.RsaOaep.Arm.DecEnd
import VerifiedGarbage.Proof.RsaOaep.Arm.DecFail
import VerifiedGarbage.Proof.RsaOaep.Arm.DecSpec
import VerifiedGarbage.Proof.RsaOaep.Arm.Label
import VerifiedGarbage.Proof.RsaPss.Arm.VfPass
import VerifiedGarbage.Proof.RsaPss.Arm.VfShift
import VerifiedGarbage.Proof.RsaPss.Arm.VfY
import VerifiedGarbage.Proof.RsaPss.Arm.YDig
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaPss.SignCases

/-!
# RSAES-OAEP decryption with SHA-224 and MGF1 with SHA-224 on ARMv7, for each implementation of the CRT

A generic file (see `TCB/Emit.lean`): `vg_rsa_oaep_sha224_mgf1_sha224_decrypt`, calling
`vg_rsa_private_checked` over an implementation `v` of `vg_rsa_private_crt`
(`Variants/RsaPrivateCrt/Arm/`), is emitted once for each, named with its
suffix, and needs its CPU features.

It uses 3624 bytes of stack: the push of the registers (56 bytes), its
frame (128 bytes) and the 3440 bytes of the call's.
-/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.Arm.RsaOaepSha224Mgf1Sha224

open VG.Proof.Rsa.Arm (CrtImpl)

def artifacts (v : CrtImpl) : List Artifact := [
  (Spec.RsaOaep.decryptApi Spec.Mgf1.sha224 Spec.Mgf1.sha224).artifact Arm.target {
    suffix := v.suffix
    notes := ["This implementation calls `" ++ Proof.Rsa.Arm.privName v ++ "`, hashes the label with \
      `vg_sha256_update` and unmasks the seed and `DB` with MGF1 calling `vg_sha256_update`. The checks of `Y`, \
      `lHash'` and the separator, the scan for it and the shift of the message to the start of `out` \
      are masks computed without branches, reading every byte of `EM` whatever the outcome; only the \
      lengths and the public key decide a branch or an address."]
    code := Proof.RsaOaep.Arm.Dec.decCode (.ofPss Proof.RsaPss.Arm.sha224) (.ofPss Proof.RsaPss.Arm.sha224) v
    stack := 3624
    verified := by exact (Proof.RsaOaep.Arm.Dec.dec_verified (.ofPss Proof.RsaPss.Arm.sha224) (.ofPss Proof.RsaPss.Arm.sha224)
      (Proof.RsaOaep.Arm.Dec.dec_sat _ _) v)
    features := v.features },
  (Spec.RsaOaep.encryptPrecomputedApi Spec.Mgf1.sha224 Spec.Mgf1.sha224).artifact Arm.target {
    suffix := v.suffix
    notes := ["ARMv7 with the selected RSA public implementation. This implementation hashes the label with `vg_sha256_update`, masks `DB` \
        and the seed with MGF1 calling `vg_sha256_update`, and calls `vg_rsa_public_precomputed_checked` \
        with the cached modulus values. The message's length is public; its bytes, the label's and \
        the seed's are only copied, hashed and masked."]
    code := Proof.RsaOaep.Arm.Enc.encryptCode (.ofPss Proof.RsaPss.Arm.sha224) (.ofPss Proof.RsaPss.Arm.sha224)
      (Proof.Rsa.Arm.pdOfCrt v)
    stack := 240
    verified := by exact (Proof.RsaOaep.Arm.Enc.encrypt_verified (.ofPss Proof.RsaPss.Arm.sha224) (.ofPss Proof.RsaPss.Arm.sha224)
      (Proof.RsaOaep.Arm.Enc.encrypt_sat_sha224 _) (Proof.Rsa.Arm.pdOfCrt v))
    features := v.features }]

end VG.Generic.RsaPrivateCrt.Arm.RsaOaepSha224Mgf1Sha224
