module

import VerifiedGarbage.Proof.RsaOaep.Arm.EncSat
public meta import VerifiedGarbage.Proof.RsaOaep.Arm.EncSat
public import VerifiedGarbage.Proof.RsaOaep.Arm.EncVerified
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Spec.RsaOaep.Precomputed
public import Init.Data.String.Defs
public import VerifiedGarbage.Spec.RsaOaep
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.Arm.PrivImpl
public import VerifiedGarbage.Proof.RsaOaep.Arm.Mgf
public import VerifiedGarbage.Proof.Rsa.Arm.PublicOfCrt
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha1
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha512_256
public import VerifiedGarbage.Proof.Framework.Registration
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
public import VerifiedGarbage.Proof.RsaOaep.Arm.DecSat
public import VerifiedGarbage.Proof.RsaOaep.Arm.DecEnd
public import VerifiedGarbage.Proof.RsaOaep.Arm.DecFail
public import VerifiedGarbage.Proof.RsaOaep.Arm.DecSpec
public import VerifiedGarbage.Proof.RsaPss.Arm.VfPass
public import VerifiedGarbage.Proof.RsaPss.Arm.VfShift
public import VerifiedGarbage.Proof.RsaPss.Arm.VfY

/-!
# RSAES-OAEP decryption with SHA-512/256 and MGF1 with SHA-1 on ARMv7, for each implementation of the CRT

A generic file (see `TCB/Emit.lean`): `vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt`, calling
`vg_rsa_private_checked` over an implementation `v` of `vg_rsa_private_crt`
(`Variants/RsaPrivateCrt/Arm/`), is emitted once for each, named with its
suffix, and needs its CPU features.

It uses 3624 bytes of stack: the push of the registers (56 bytes), its
frame (128 bytes) and the 3440 bytes of the call's.
-/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.Arm.RsaOaepSha512_256Mgf1Sha1

open VG.Proof.Rsa.Arm (CrtImpl)

def artifacts (v : CrtImpl) : List Artifact := [
  (Spec.RsaOaep.decryptApi Spec.Mgf1.sha512_256 Spec.Mgf1.sha1).artifact Arm.target {
    suffix := v.suffix
    notes := ["This implementation calls `" ++ Proof.Rsa.Arm.privName v ++ "`, hashes the label with \
      `vg_sha512_update` and unmasks the seed and `DB` with MGF1 calling `vg_sha1_update`. The checks of `Y`, \
      `lHash'` and the separator, the scan for it and the shift of the message to the start of `out` \
      are masks computed without branches, reading every byte of `EM` whatever the outcome; only the \
      lengths and the public key decide a branch or an address."]
    code := Proof.RsaOaep.Arm.Dec.decCode (.ofPss Proof.RsaPss.Arm.sha512_256) (.ofPss Proof.RsaPss.Arm.sha1) v
    stack := 3624
    verified := (Proof.RsaOaep.Arm.Dec.dec_verified (.ofPss Proof.RsaPss.Arm.sha512_256) (.ofPss Proof.RsaPss.Arm.sha1)
      (Proof.RsaOaep.Arm.Dec.dec_sat _ _) v)
    features := v.features },
  (Spec.RsaOaep.encryptPrecomputedApi Spec.Mgf1.sha512_256 Spec.Mgf1.sha1).artifact Arm.target {
    suffix := v.suffix
    notes := ["ARMv7 with the selected RSA public implementation. This implementation hashes the label with `vg_sha512_update`, masks `DB` \
        and the seed with MGF1 calling `vg_sha1_update`, and calls `vg_rsa_public_precomputed_checked` \
        with the cached modulus values. The message's length is public; its bytes, the label's and \
        the seed's are only copied, hashed and masked."]
    code := Proof.RsaOaep.Arm.Enc.encryptCode (.ofPss Proof.RsaPss.Arm.sha512_256) (.ofPss Proof.RsaPss.Arm.sha1)
      (Proof.Rsa.Arm.pdOfCrt v)
    stack := 240
    verified := (Proof.RsaOaep.Arm.Enc.encrypt_verified (.ofPss Proof.RsaPss.Arm.sha512_256) (.ofPss Proof.RsaPss.Arm.sha1)
      (Proof.RsaOaep.Arm.Enc.encrypt_sat_sha512_256 _) (Proof.Rsa.Arm.pdOfCrt v))
    features := v.features }]

end VG.Generic.RsaPrivateCrt.Arm.RsaOaepSha512_256Mgf1Sha1
