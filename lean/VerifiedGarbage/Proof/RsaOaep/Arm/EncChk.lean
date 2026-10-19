module

public import VerifiedGarbage.Proof.RsaOaep.Arm.EncBase
public import VerifiedGarbage.Proof.RsaOaep.Arm.Mgf
import VerifiedGarbage.Proof.RsaOaep.Encode
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Impl.RsaOaep.Arm
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
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
import VerifiedGarbage.Proof.RsaOaep.Arm.Label
import VerifiedGarbage.Proof.RsaOaep.Decode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
import VerifiedGarbage.Proof.RsaPss.Arm.CtMgfLoop
import VerifiedGarbage.Proof.RsaPss.Arm.CtPad
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Sha256.StateMem

/-!
# RSAES-OAEP encryption with a precomputed public key on ARMv7: the checks

`chk_vp`: `scratch` to its slot, and the flags of whether the message fits
(`fits`), from the lengths alone. `fail_vp`: when it does not, zeros to
`out` and 0 returned, as `encrypt` (`Proof.RsaOaep.encrypt_none`) says.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Enc

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa arg)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h g : OHash)

/-- A state of the body. -/
abbrev S (P : EP) (σ s : State) : Prop := In h.H.D P σ ∧ (P.lay h.H.D).St σ s

/-- The label, the message and the seed, as they are in the run from `σ`. -/
abbrev labB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.lab) P.ll
abbrev msgB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.msg) P.ml
abbrev seedB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.seed) h.H.D

/-- Whether the message fits. -/
abbrev fits (P : EP) : Prop := 2 * h.H.D + 2 + P.ml ≤ P.K

/-- What the function writes to `out` and returns. -/
abbrev Res (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.Rsa.publicPrecompute P.nB = some P.pw →
    Spec.Rsa.written m (State.addr P.out) P.K r (Spec.RsaOaep.encrypt h.G g.G P.nB P.eB (labB P σ) (msgB P σ)
      (seedB h P σ))

/-- The end of the body. -/
abbrev Fin (P : EP) (σ s : State) : Prop := S h P σ s ∧ Res h g P σ s.mem (s.gpr .r0)

theorem arg_lt {j : Nat} (hj : j < 15) : arg j < 4096 := by
  unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega

/-- An argument: its place, readable, and its value. -/
theorem argAt {D : Nat} {P : EP} {σ s : State} (hi : In D P σ) (hs : (P.lay D).St σ s) {j : Nat} (hj : j < 15) :
    State.addr (P.B + BitVec.ofNat 32 (arg j)) = (P.lay D).fr (arg j) ∧
    InRegions (s.rd ++ s.wr) ((P.lay D).fr (arg j)) 4 ∧
    s.mem.readW ((P.lay D).fr (arg j)) 32 = P.argv.getD j 0 := by
  have hl : j < (P.lay D).argv.length := by simp only [EP.argv, List.length_cons, List.length_nil]; omega
  exact ⟨hi.ok.addrB (by
      show arg j < frameBytes + 56 + 44; unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega),
    by rw [hs.rd, hs.wr]; exact hi.ok.arg_read hl, hs.arg hl⟩

/-- A slot, written with `r12 = sp`. -/
theorem slotAt {D : Nat} {P : EP} {σ : State} (hi : In D P σ) {d : Nat} (hd : d + 4 ≤ frameBytes) :
    State.addr (P.B + BitVec.ofNat 32 d) = (P.lay D).fr d :=
  hi.ok.addrB (by show d < frameBytes + 56 + 44; unfold frameBytes at hd ⊢; omega)

/-- The flags of the checks: zero exactly when `c + ml ≤ K`. -/
theorem chk_z {K c ml : Nat} (hK : K ≤ 1024) (hc1 : 1 ≤ c) (hc : c ≤ 1024) (hml : ml < 2 ^ 32) :
    (((BitVec.ofNat 32 K - BitVec.ofNat 32 c) >>> 31 ||| BitVec.ofNat 32 ml >>> 10 |||
      (BitVec.ofNat 32 K - BitVec.ofNat 32 c - BitVec.ofNat 32 ml) >>> 31) - 0 == 0) = decide (c + ml ≤ K) := by
  simp only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero]
  by_cases hcK : c ≤ K
  · rw [Offset.ofNat_sub_ofNat (w := 32) hcK]
    have z1 : BitVec.ofNat 32 (K - c) >>> 31 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; simp; omega
    by_cases hm : ml < 1024
    · have z2 : BitVec.ofNat 32 ml >>> 10 = 0 := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; simp; omega
      rw [z1, z2, ltBit (a := K - c) (b := ml) (by omega) (by omega)]
      by_cases e : K - c < ml
      · simp [e]; omega
      · simp [e]; omega
    · have hne : BitVec.ofNat 32 ml >>> 10 ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow] at this; simp at this; omega
      rw [decide_eq_false (by omega)]
      exact beq_false_of_ne fun e => hne ((or_eq_zero32 _ _).1 ((or_eq_zero32 _ _).1 e).1).2
  · have hne : (BitVec.ofNat 32 K - BitVec.ofNat 32 c) >>> 31 ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (a := K) (by omega), Nat.mod_eq_of_lt (a := c) (by omega)] at this
      simp at this; omega
    rw [decide_eq_false (by omega)]
    exact beq_false_of_ne fun e => hne ((or_eq_zero32 _ _).1 ((or_eq_zero32 _ _).1 e).1).1

/-! ## The checks -/

/-- After `encChk`. -/
abbrev C0 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.H.D) P.scr σ s ∧ In h.H.D P σ ∧ s.z = decide (fits h P)

theorem chk_vp (P : EP) : VP (S h P) (.block (encChk h.H)) (C0 h P) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.2.sp.trans h₂.2.sp.symm) fun σ s ⟨hi, hs⟩ => ?_
  have hD := h.D_le
  have hK := hi.k1024
  obtain ⟨a11, r11, v11⟩ := argAt hi hs (j := 11) (by decide)
  obtain ⟨a3, r3, v3⟩ := argAt hi hs (j := 3) (by decide)
  obtain ⟨a9, r9, v9⟩ := argAt hi hs (j := 9) (by decide)
  replace v11 : s.mem.readW ((P.lay h.H.D).fr (arg 11)) 32 = P.scr := v11
  replace v3 : s.mem.readW ((P.lay h.H.D).fr (arg 3)) 32 = BitVec.ofNat 32 P.K := v3
  replace v9 : s.mem.readW ((P.lay h.H.D).fr (arg 9)) 32 = BitVec.ofNat 32 P.ml := v9
  have k : ∀ (j : Nat) (v : BitVec 32), j < 15 →
      (s.mem.writeW ((P.lay h.H.D).fr sS) v).readW ((P.lay h.H.D).fr (arg j)) 32 =
        s.mem.readW ((P.lay h.H.D).fr (arg j)) 32 :=
    fun j v hj => Lay.readW_fr_other _ _ _ (by
      unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes sS; split <;> omega) (by
      unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega) (by decide)
  have hw : WP isa (.block (encChk h.H)) s fun t => t.mem = s.mem.writeW ((P.lay h.H.D).fr sS) P.scr ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.z = decide (fits h P) := by
    prun [encChk, sp0, ld, st, mw, hs.sp, a11, r11, v11, a3, r3, v3, a9, r9, v9, k 3 _ (by decide),
      k 9 _ (by decide), slotAt hi (d := sS) (by decide), hs.inFr (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes; decide),
      arg_lt, movw_val (show 2 * h.H.D + 2 < 2 ^ 16 by omega), dpVal, chk_z hK (show 1 ≤ 2 * h.H.D + 2 by omega) (show 2 * h.H.D + 2 ≤ 1024 by omega) hi.ml32]
  refine WP.mono hw fun t ⟨m, rd, wr, sp, z⟩ => ⟨⟨?_, ?_⟩, hi, z⟩
  · exact hs.frameW (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes; decide) (by
      rw [m]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)) rd wr sp
  · rw [m, Mem.readW_writeW_self32]

/-! ## A message that does not fit -/

theorem out_wbuf {P : EP} {σ : State} (hi : In h.H.D P σ) : WBuf (P.lay h.H.D) P.out P.K := by
  have hK := hi.k1024
  have hf := hi.ok.fits P.OUT (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hf
  exact ⟨hf, by omega, ⟨P.OUT, by simp, Region.contains_self _ _⟩,
    hi.ok.stk_fr (R := P.OUT) (.inr (by simp)) (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes + 56; decide)⟩

theorem nB_length {D : Nat} {P : EP} {σ : State} (hi : In D P σ) : P.nB.length = P.K := by
  rw [← hi.nB]; simp [Spec.Rsa.bytesAt]

theorem msgB_length (P : EP) (σ : State) : (msgB P σ).length = P.ml := by simp [Spec.Rsa.bytesAt]

theorem fail_vp (P : EP) :
    VP (fun σ s => C0 h P σ s ∧ isa.eval .ne s = some true) (encFail) (Fin h g P) := by
  by_cases hP : ∃ σ, In h.H.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hb := out_wbuf h hi₀
  have hK := hi₀.k64
  show VP _ (.seq (.block [sp0, ld .r0 (arg 0), ld .lr (arg 3), mw .r2 0]) (.seq Impl.Bignum.Arm.maskBytes
    (.block [mw .r0 0]))) _
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.H.D) P.scr σ s ∧ (In h.H.D P σ ∧ ¬ fits h P)) ∧ s.gpr .r0 = P.out ∧
      s.gpr .r2 = 0 ∧ s.gpr .lr = BitVec.ofNat 32 P.K)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm)
      fun σ s ⟨⟨hc, hi, z⟩, e⟩ => ?_) ?_
  · have nf : ¬ fits h P := by
      intro hf
      rw [VG.Proof.X25519.Arm.eval_ne, z, decide_eq_true hf] at e
      cases e
    obtain ⟨a0, r0, v0⟩ := argAt hi hc.st (j := 0) (by decide)
    obtain ⟨a3, r3, v3⟩ := argAt hi hc.st (j := 3) (by decide)
    replace v0 : s.mem.readW ((P.lay h.H.D).fr (arg 0)) 32 = P.out := v0
    replace v3 : s.mem.readW ((P.lay h.H.D).fr (arg 3)) 32 = BitVec.ofNat 32 P.K := v3
    have hw : WP isa (.block [sp0, ld .r0 (arg 0), ld .lr (arg 3), mw .r2 0]) s fun t => t.mem = s.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr .r0 = P.out ∧ t.gpr .r2 = 0 ∧
        t.gpr .lr = BitVec.ofNat 32 P.K := by
      prun [sp0, ld, mw, hc.st.sp, a0, r0, v0, a3, r3, v3, arg_lt]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, t0, t2, tl⟩ => ⟨⟨hc.regs rd wr sp m, hi, nf⟩, t0, t2, tl⟩
  refine VP.seq ((zero_vp hb (by omega) (Inv := fun σ _ => In h.H.D P σ ∧ ¬ fits h P)
    fun σ m m' hm _ => hm).mono (fun σ s ⟨⟨hc, hm⟩, r0, r2, lr⟩ => ⟨hc, hm, r0, r2, lr⟩) fun _ _ h => h) ?_
  refine VP.taint [] ⟨_, by taint_decide⟩ (fun _ _ _ _ _ _ r hr => by simp at hr)
    fun σ s ⟨hc, ⟨hi, nf⟩, hz⟩ => ?_
  apply WP.of_runBlock
  simp only [mw, runBlock_cons, runStep_some, runBlock_nil, exec]
  refine ⟨_, rfl, ⟨hi, hc.st.regs rfl rfl rfl rfl⟩, fun _ => ?_⟩
  have en : Spec.RsaOaep.encrypt h.G g.G P.nB P.eB (labB P σ) (msgB P σ) (seedB h P σ) = none :=
    Proof.RsaOaep.encrypt_none (by rw [nB_length hi, msgB_length, h.glen]; simp only [fits] at nf; omega)
  rw [en]
  refine ⟨by simp [VG.Arm.RegUpd.gpr_setReg], ?_⟩
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i h1 _
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h1
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
  exact hz i h1

end VG.Proof.RsaOaep.Arm.Enc
