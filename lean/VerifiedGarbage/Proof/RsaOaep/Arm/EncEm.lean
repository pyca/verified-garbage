module

public import VerifiedGarbage.Proof.RsaOaep.Arm.EncChk
public import VerifiedGarbage.Proof.RsaOaep.Encode
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Impl.RsaOaep.Arm
import VerifiedGarbage.Proof.RsaOaep.Arm.Label
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
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
import VerifiedGarbage.Proof.RsaOaep.Decode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
import VerifiedGarbage.Proof.RsaPss.Arm.CtMgfLoop
import VerifiedGarbage.Proof.RsaPss.Arm.CtPad
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Sha256.StateMem

/-!
# RSAES-OAEP encryption with a precomputed public key on ARMv7: `EM` before masking

When the message fits: `EM`'s `k` bytes at `scratch + oEm` cleared, the
seed after its first byte, the label's hash (`label_vp`) after the seed,
`0x01` before the message and the message at its end: `EM = 0x00 ‖ seed ‖
lHash ‖ 0… ‖ 0x01 ‖ M` (`Proof.RsaOaep.EmAt`, `em_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Enc

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa arg put1)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h : OHash)

/-- A state of the body when the message fits. -/
abbrev E0 (P : EP) (σ s : State) : Prop := Ctx (P.lay h.H.D) P.scr σ s ∧ In h.H.D P σ ∧ fits h P

/-- `EM`'s bytes, from the memory. -/
abbrev emV (scr : BitVec 32) (m : Mem) (o : Nat) : Byte := m (sa scr (oEm + o))

/-- The label's hash. -/
abbrev lhB (P : EP) (σ : State) : List Byte := h.G.hash (labB P σ)

/-- The facts that do not change in the body. -/
abbrev K0 (P : EP) (σ : State) : Prop := In h.H.D P σ ∧ fits h P

section
variable {P : EP} {σ : State}

theorem K0.hg (k : K0 h P σ) : Geo (P.lay h.H.D) P.scr := k.1.geo
theorem K0.kD (k : K0 h P σ) : 2 * h.H.D + 2 + P.ml ≤ P.K ∧ P.K ≤ 1024 ∧ 64 ≤ P.K ∧ 0 < h.H.D ∧ h.H.D ≤ 64 :=
  ⟨k.2, k.1.k1024, k.1.k64, h.D_pos, h.D_le⟩

end

/-- The arguments read in this file. -/
theorem argV {P : EP} {σ s : State} (hi : In h.H.D P σ) (hs : (P.lay h.H.D).St σ s) :
    (State.addr (P.B + BitVec.ofNat 32 (arg 3)) = (P.lay h.H.D).fr (arg 3) ∧
      InRegions (s.rd ++ s.wr) ((P.lay h.H.D).fr (arg 3)) 4 ∧
      s.mem.readW ((P.lay h.H.D).fr (arg 3)) 32 = BitVec.ofNat 32 P.K) ∧
    (State.addr (P.B + BitVec.ofNat 32 (arg 8)) = (P.lay h.H.D).fr (arg 8) ∧
      InRegions (s.rd ++ s.wr) ((P.lay h.H.D).fr (arg 8)) 4 ∧ s.mem.readW ((P.lay h.H.D).fr (arg 8)) 32 = P.msg) ∧
    (State.addr (P.B + BitVec.ofNat 32 (arg 9)) = (P.lay h.H.D).fr (arg 9) ∧
      InRegions (s.rd ++ s.wr) ((P.lay h.H.D).fr (arg 9)) 4 ∧
      s.mem.readW ((P.lay h.H.D).fr (arg 9)) 32 = BitVec.ofNat 32 P.ml) ∧
    (State.addr (P.B + BitVec.ofNat 32 (arg 10)) = (P.lay h.H.D).fr (arg 10) ∧
      InRegions (s.rd ++ s.wr) ((P.lay h.H.D).fr (arg 10)) 4 ∧
      s.mem.readW ((P.lay h.H.D).fr (arg 10)) 32 = P.seed) :=
  ⟨argAt hi hs (by decide), argAt hi hs (by decide), argAt hi hs (by decide), argAt hi hs (by decide)⟩

/-! ## The pieces -/

/-- `EM` cleared. -/
abbrev Z1 (P : EP) (m : Mem) : Prop := ∀ i < P.K, emV P.scr m i = 0

theorem em1_vp (P : EP) :
    VP (E0 h P) (.seq (.block clrEm) Impl.Bignum.Arm.maskBytes) (fun σ s => E0 h P σ s ∧ Z1 P s.mem) := by
  by_cases hP : ∃ σ, In h.H.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have hK0 := hi₀.k64
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.H.D) P.scr σ s ∧ K0 h P σ) ∧ s.gpr .r0 = P.scr + BitVec.ofNat 32 oEm ∧
      s.gpr .r2 = 0 ∧ s.gpr .lr = BitVec.ofNat 32 P.K)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hi, hf⟩ => ?_)
    ((zero_vp (hg.wbuf (o := oEm) (n := P.K) (by oomega) (by omega)) (by omega) (Inv := fun σ _ => K0 h P σ)
      fun σ m m' hm _ => hm).mono (fun σ s ⟨⟨hc, hm⟩, r0, r2, lr⟩ => ⟨hc, hm, r0, r2, lr⟩)
      fun σ s ⟨hc, hm, hz⟩ => ⟨⟨hc, hm⟩, fun i hi => by rw [emV, ← hg.byteAt_scr (by oomega)]; exact hz i hi⟩)
  obtain ⟨⟨a3, r3, v3⟩, -⟩ := argV h hi hc.st
  have hw : WP isa (.block clrEm) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.gpr .r0 = P.scr + BitVec.ofNat 32 oEm ∧ t.gpr .r2 = 0 ∧ t.gpr .lr = BitVec.ofNat 32 P.K := by
    prun [clrEm, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a3, r3, v3, arg_lt,
      movw_val (show oEm < 2 ^ 16 by decide)]
  exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r2, lr⟩ => ⟨⟨hc.regs rd wr sp m, hi, hf⟩, r0, r2, lr⟩

/-- The seed after `EM`'s first byte, zeros elsewhere. -/
abbrev Z2 (P : EP) (sd : List Byte) (m : Mem) : Prop :=
  emV P.scr m 0 = 0 ∧ (∀ i < h.H.D, emV P.scr m (1 + i) = sd.getD i 0) ∧
    ∀ i, 1 + h.H.D ≤ i → i < P.K → emV P.scr m i = 0

/-- The seed's bytes, in a state of the body. -/
theorem seed_bytes {P : EP} {σ s : State} (hs : (P.lay h.H.D).St σ s) :
    ∀ i < h.H.D, s.mem (byteAt P.seed i) = (seedB h P σ).getD i 0 := by
  intro i hi
  have e := hs.ro (R := P.SEED h.H.D) (by simp)
  have e2 := congrArg (fun l => l.getD i 0) e
  simp only [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some] at e2
  simp only [seedB, Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some, byteAt]
  exact e2

theorem em2_vp (P : EP) :
    VP (fun σ s => E0 h P σ s ∧ Z1 P s.mem) (.seq (.block (seedSet h.H)) Impl.Bignum.Arm.copyBytes)
      (fun σ s => E0 h P σ s ∧ Z2 h P (seedB h P σ) s.mem) := by
  by_cases hP : ∃ σ, In h.H.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have hD := h.D_le
  have hD0 := h.D_pos
  obtain ⟨σ', ok⟩ := hg.ok
  have hsd : RBuf (P.lay h.H.D) P.seed h.H.D := by
    have hf := hi₀.ok.fits (P.SEED h.H.D) (by simp)
    simp only [Proof.X25519.Arm.addr_toNat] at hf
    exact ⟨hf, by omega, ⟨P.SEED h.H.D, by simp, Region.contains_self _ _⟩⟩
  have sep : Region.Disjoint ⟨State.addr P.seed, h.H.D⟩ ⟨State.addr (P.scr + BitVec.ofNat 32 (oEm + 1)), h.H.D⟩ := by
    rw [hg.addr (by oomega)]
    exact (ok.rw_ro (w := P.SCR) (r := P.SEED h.H.D) (by simp) (by simp)).symm.sub_right
      (Offset.sub_base _ (by have := hi₀.pubScr.2; oomega))
  -- What the copy keeps: `EM`'s other bytes, zero.
  let X : State → Mem → Prop := fun σ m => K0 h P σ ∧ emV P.scr m 0 = 0 ∧
    ∀ i, 1 + h.H.D ≤ i → i < P.K → emV P.scr m i = 0
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.H.D) P.scr σ s ∧ X σ s.mem) ∧
      s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + 1) ∧ s.gpr .r1 = P.seed ∧ s.gpr .lr = BitVec.ofNat 32 h.H.D ∧
      ∀ i < h.H.D, s.mem (byteAt P.seed i) = (seedB h P σ).getD i 0)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm)
      fun σ s ⟨⟨hc, hi, hf⟩, hz⟩ => ?_)
    ((copy_vp (hg.wbuf (o := oEm + 1) (n := h.H.D) (by oomega) hD0) hsd sep hD0 (Inv := X)
      (f := fun σ i => (seedB h P σ).getD i 0) fun σ m m' ⟨k, z0, zr⟩ hf => ?_).mono
      (fun σ s ⟨⟨hc, hm⟩, r0, r1, lr, hb⟩ => ⟨hc, hm, r0, r1, lr, hb⟩)
      fun σ s ⟨hc, ⟨k, z0, zr⟩, hb⟩ => ⟨⟨hc, k⟩, z0, fun i hi => ?_, zr⟩)
  · obtain ⟨-, -, -, ⟨a10, r10, v10⟩⟩ := argV h hi hc.st
    have hw : WP isa (.block (seedSet h.H)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + 1) ∧ t.gpr .r1 = P.seed ∧ t.gpr .lr = BitVec.ofNat 32 h.H.D := by
      prun [seedSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a10, r10, v10, arg_lt,
        movw_val (show oEm + 1 < 2 ^ 16 by decide), movw_val (show h.H.D < 2 ^ 16 by omega)]
    refine WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr⟩ => ⟨⟨hc.regs rd wr sp m, ⟨hi, hf⟩, ?_, fun i h1 h2 => ?_⟩,
      r0, r1, lr, ?_⟩
    · rw [emV, m]; exact hz 0 (by omega)
    · rw [emV, m]; exact hz i h2
    · rw [m]; exact seed_bytes h hc.st
  · rw [hg.addr (by oomega)] at hf
    refine ⟨k, ?_, fun i h1 h2 => ?_⟩
    · rw [emV, ← z0]
      exact hf _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := P.scr) (o := oEm + 0) (n := 1) (by oomega) (by oomega) (by oomega) _
          (Region.contains_self _ _)
    · rw [emV, ← zr i h1 h2]
      exact hf _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by oomega) (by oomega) (by oomega) _
          (Region.contains_self _ _)
  · rw [emV, show oEm + (1 + i) = oEm + 1 + i by oomega, ← hg.byteAt_scr (by oomega)]
    exact hb i hi

/-! ## `EM`'s bytes as functions -/

/-- `EM`'s first `k` bytes are `f`. -/
abbrev EMv (P : EP) (m : Mem) (f : Nat → Byte) : Prop := ∀ i < P.K, emV P.scr m i = f i

/-- `EM` with the seed. -/
abbrev e2 (P : EP) (σ : State) (i : Nat) : Byte :=
  if 1 ≤ i ∧ i < 1 + h.H.D then (seedB h P σ).getD (i - 1) 0 else 0

/-- `EM` with the seed and `lHash`. -/
abbrev e3 (P : EP) (σ : State) (i : Nat) : Byte :=
  if 1 + h.H.D ≤ i ∧ i < 1 + 2 * h.H.D then (lhB h P σ).getD (i - (1 + h.H.D)) 0 else e2 h P σ i

/-- `EM` with `0x01`. -/
abbrev e4 (P : EP) (σ : State) (i : Nat) : Byte := if i = P.K - P.ml - 1 then 1 else e3 h P σ i

/-- `EM` before masking. -/
abbrev e5 (P : EP) (σ : State) (i : Nat) : Byte :=
  if P.K - P.ml ≤ i ∧ i < P.K then (msgB P σ).getD (i - (P.K - P.ml)) 0 else e4 h P σ i

theorem z2_emv {P : EP} {σ : State} {m : Mem} (hz : Z2 h P (seedB h P σ) m) : EMv P m (e2 h P σ) := by
  intro i hi
  obtain ⟨z0, sd, zr⟩ := hz
  simp only [e2]
  by_cases h1 : 1 ≤ i ∧ i < 1 + h.H.D
  · rw [ite_eq_left h1, show i = 1 + (i - 1) by omega, sd _ (by omega), Nat.add_sub_cancel_left]
  · rw [ite_eq_right h1]
    by_cases h0 : i = 0
    · subst h0; exact z0
    · exact zr i (by omega) hi

theorem add_ofNat_sub {x : BitVec 32} {a b : Nat} (hb : b ≤ a) :
    x + BitVec.ofNat 32 a - BitVec.ofNat 32 b = x + BitVec.ofNat 32 (a - b) := by
  have : BitVec.ofNat 32 a = BitVec.ofNat 32 (a - b) + BitVec.ofNat 32 b := by
    rw [BitVec.ofNat_add_ofNat, Nat.sub_add_cancel hb]
  rw [this, ← BitVec.add_assoc, BitVec.add_sub_cancel]

theorem add_ofNat_sub_one {x : BitVec 32} {a : Nat} (ha : 1 ≤ a) :
    x + BitVec.ofNat 32 a - 1 = x + BitVec.ofNat 32 (a - 1) := add_ofNat_sub ha

/-- `EM`'s bytes, kept by a write elsewhere in our part of `scratch`. -/
theorem emv_keep {P : EP} (hg : Geo (P.lay h.H.D) P.scr) (hK : P.K ≤ 1024) {m m' : Mem} {f : Nat → Byte}
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (∃ o n, oBuf ≤ o ∧ o + n ≤ oRsa ∧ r = sR P.scr o n) ∨
      r = (P.lay h.H.D).LOW) (he : EMv P m f) : EMv P m' f := by
  obtain ⟨σ', ok⟩ := hg.ok
  intro i hi
  rw [emV, ← he i hi]
  refine hf _ fun r hr => ?_
  rcases hd r hr with ⟨o, n, h1, h2, rfl⟩ | rfl
  · exact Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by oomega) (by oomega) h2 _ (Region.contains_self _ _)
  · exact hg.low ok (o := oEm + i) (n := 1) (by oomega) _ (Region.contains_self _ _)

/-- The label's hash at `oDig`. -/
theorem em3_vp (P : EP) :
    VP (fun σ s => E0 h P σ s ∧ Z2 h P (seedB h P σ) s.mem) (hashLabel h.H 6 oDig)
      (fun σ s => E0 h P σ s ∧ EMv P s.mem (e2 h P σ) ∧
        ∀ i < h.H.D, s.mem (sa P.scr (oDig + i)) = (lhB h P σ).getD i 0) := by
  by_cases hP : ∃ σ, In h.H.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have := h.S_le; have := h.Wb_le; have := h.F_le
  obtain ⟨σ', ok⟩ := hg.ok
  have hl := hi₀.ok.fits P.LAB (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hl
  have hlab : RBuf (P.lay h.H.D) P.lab P.ll := ⟨hl, hi₀.ll32, ⟨P.LAB, by simp, Region.contains_self _ _⟩⟩
  have dS : ∀ {o n : Nat}, o + n ≤ oRsa → Region.Disjoint ⟨State.addr P.lab, P.ll⟩ (sR P.scr o n) :=
    fun hon => (hg.ro ok hon (R := P.LAB) (by simp)).symm
  refine (label_vp hg h (j := 6) (o := oDig) (ll := P.ll) (lab := P.lab) (by simp) (arg_lt (by decide))
    (arg_lt (by decide)) rfl rfl hlab (dS (by oomega)) (dS (by oomega))
    (ok.low_buf (R := P.LAB) (.inl (by simp))).symm (by oomega) (by oomega) (labB := labB P)
    (fun σ s hc => hc.st.ro (R := P.LAB) (by simp))
    (Inv := fun σ m => K0 h P σ ∧ EMv P m (e2 h P σ)) fun σ m m' ⟨k, he⟩ hf => ⟨k, emv_keep h hg hK hf ?_ he⟩).mono
    (fun σ s ⟨⟨hc, hi, hf⟩, hz⟩ => ⟨hc, ⟨hi, hf⟩, z2_emv h hz⟩)
    fun σ s ⟨hc, ⟨⟨hi, hf⟩, he⟩, hd⟩ => ⟨⟨hc, hi, hf⟩, he, hd⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inl ⟨oSt, h.H.S, by oomega, by oomega, rfl⟩
  · exact .inl ⟨oW, h.ok.Wb, by oomega, by oomega, rfl⟩
  · exact .inr rfl
  · exact .inl ⟨oDig, h.H.F, by oomega, by oomega, rfl⟩

/-- `lHash` after the seed. -/
theorem em4_vp (P : EP) :
    VP (fun σ s => E0 h P σ s ∧ EMv P s.mem (e2 h P σ) ∧
        ∀ i < h.H.D, s.mem (sa P.scr (oDig + i)) = (lhB h P σ).getD i 0)
      (.seq (.block (lhSet h.H)) Impl.Bignum.Arm.copyBytes)
      (fun σ s => E0 h P σ s ∧ EMv P s.mem (e3 h P σ)) := by
  by_cases hP : ∃ σ, In h.H.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have hD := h.D_le
  have hD0 := h.D_pos
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s hs => hf hs.1.2.2
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  let X : State → Mem → Prop := fun σ m => K0 h P σ ∧
    ∀ i < P.K, (i < 1 + h.H.D ∨ 1 + 2 * h.H.D ≤ i) → emV P.scr m i = e2 h P σ i
  have sp4 : Region.Disjoint ⟨State.addr (P.scr + BitVec.ofNat 32 oDig), h.H.D⟩
      ⟨State.addr (P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D)), h.H.D⟩ := by
    rw [hg.addr (by oomega), hg.addr (by oomega)]
    exact Geo.sep (by oomega) (by oomega) (by oomega)
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.H.D) P.scr σ s ∧ X σ s.mem) ∧
      s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D) ∧ s.gpr .r1 = P.scr + BitVec.ofNat 32 oDig ∧
      s.gpr .lr = BitVec.ofNat 32 h.H.D ∧
      ∀ i < h.H.D, s.mem (byteAt (P.scr + BitVec.ofNat 32 oDig) i) = (lhB h P σ).getD i 0)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm)
      fun σ s ⟨⟨hc, hi, _⟩, he, hd⟩ => ?_)
    ((copy_vp (hg.wbuf (o := oEm + 1 + h.H.D) (n := h.H.D) (by oomega) hD0) (hg.rbuf (o := oDig) (n := h.H.D)
      (by oomega) hD0) sp4 hD0 (Inv := X) (f := fun σ i => (lhB h P σ).getD i 0) fun σ m m' ⟨k, ho⟩ hf' => ?_).mono
      (fun σ s ⟨⟨hc, hm⟩, r0, r1, lr, hb⟩ => ⟨hc, hm, r0, r1, lr, hb⟩)
      fun σ s ⟨hc, ⟨k, ho⟩, hb⟩ => ⟨⟨hc, k⟩, fun i hi => ?_⟩)
  · have hw : WP isa (.block (lhSet h.H)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D) ∧ t.gpr .r1 = P.scr + BitVec.ofNat 32 oDig ∧
        t.gpr .lr = BitVec.ofNat 32 h.H.D := by
      prun [lhSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS,
        movw_val (show oEm + 1 + h.H.D < 2 ^ 16 by oomega), movw_val (show oDig < 2 ^ 16 by decide),
        movw_val (show h.H.D < 2 ^ 16 by omega)]
    refine WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr⟩ => ⟨⟨hc.regs rd wr sp m, ⟨hi, hf⟩, fun i hi _ => ?_⟩,
      r0, r1, lr, fun i hi => ?_⟩
    · rw [m]; exact he i hi
    · rw [m, hg.byteAt_scr (by oomega)]; exact hd i hi
  · rw [hg.addr (by oomega)] at hf'
    refine ⟨k, fun i hi hr => ?_⟩
    rw [emV, ← ho i hi hr]
    exact hf' _ fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by oomega) (by oomega) (by oomega) _
        (Region.contains_self _ _)
  · simp only [e3]
    by_cases hr : 1 + h.H.D ≤ i ∧ i < 1 + 2 * h.H.D
    · rw [ite_eq_left hr, emV, show oEm + i = oEm + 1 + h.H.D + (i - (1 + h.H.D)) by oomega,
        ← hg.byteAt_scr (by oomega)]
      exact hb _ (by omega)
    · rw [ite_eq_right hr]; exact ho i hi (by omega)

theorem put1_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .lr])
    (.block put1) hc).isSome = true := ⟨_, by taint_decide⟩

/-- `0x01` before the message's place at the end of `EM`. -/
theorem em5_vp (P : EP) :
    VP (fun σ s => E0 h P σ s ∧ EMv P s.mem (e3 h P σ)) (.seq (.block msgPos) (.block put1))
      (fun σ s => (E0 h P σ s ∧ EMv P s.mem (e4 h P σ)) ∧
        s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + (P.K - P.ml)) ∧ s.gpr .r1 = P.msg ∧
        s.gpr .lr = BitVec.ofNat 32 P.ml ∧ s.z = decide (P.ml = 0)) := by
  by_cases hP : ∃ σ, In h.H.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have hD := h.D_le
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s hs => hf hs.1.2.2
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  refine VP.seq (G := fun σ s => (E0 h P σ s ∧ EMv P s.mem (e3 h P σ)) ∧
      s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + (P.K - P.ml - 1)) ∧ s.gpr .r1 = P.msg ∧
      s.gpr .lr = BitVec.ofNat 32 P.ml)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm)
      fun σ s ⟨⟨hc, hi, hf'⟩, he⟩ => ?_)
    (VP.taint _ put1_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨⟨⟨hc, hi, hf'⟩, he⟩, r0, r1, lr⟩ => ?_)
  · obtain ⟨⟨a3, r3, v3⟩, ⟨a8, r8, v8⟩, ⟨a9, r9, v9⟩, -⟩ := argV h hi hc.st
    have hw : WP isa (.block msgPos) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + (P.K - P.ml - 1)) ∧ t.gpr .r1 = P.msg ∧
        t.gpr .lr = BitVec.ofNat 32 P.ml := by
      prun [msgPos, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a3, r3, v3, a8, r8, v8, a9, r9, v9,
        arg_lt, movw_val (show oEm < 2 ^ 16 by decide), BitVec.add_assoc, BitVec.ofNat_add_ofNat,
        add_ofNat_sub (x := P.scr) (a := oEm + P.K) (b := P.ml) (by omega),
        add_ofNat_sub_one (x := P.scr) (a := oEm + P.K - P.ml) (by oomega)]
      rw [show oEm + P.K - P.ml - 1 = oEm + (P.K - P.ml - 1) by oomega]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr⟩ => ⟨⟨⟨hc.regs rd wr sp m, hi, hf'⟩, m ▸ he⟩, r0, r1, lr⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
  · have ad : State.addr (P.scr + BitVec.ofNat 32 (oEm + (P.K - P.ml - 1))) = sa P.scr (oEm + (P.K - P.ml - 1)) :=
      hg.addr (by oomega)
    have wd : InRegions s.wr (sa P.scr (oEm + (P.K - P.ml - 1))) 1 := hg.wr hc.st (by oomega)
    have hz0 : ∀ y : BitVec 32, y - 0 = y := fun y => BitVec.sub_zero y
    have hw : WP isa (.block put1) s fun t =>
        t.mem = s.mem.writeW (sa P.scr (oEm + (P.K - P.ml - 1))) (1 : Byte) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.sp = s.sp ∧ t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + (P.K - P.ml - 1) + 1) ∧
        t.gpr .r1 = P.msg ∧ t.gpr .lr = BitVec.ofNat 32 P.ml ∧ t.z = decide (P.ml = 0) := by
      prun [put1, mw, r0, r1, lr, ad, wd, movw_val (show 1 < 2 ^ 16 by decide), dpVal, hz0,
        VG.Proof.X25519.Arm.ofNat_beq_zero hi.ml32, BitVec.add_assoc, VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32]
      rfl
    refine WP.mono hw fun t ⟨m, rd, wr, sp, t0, t1, tl, z⟩ => ?_
    have fr : Frame [sR P.scr (oEm + (P.K - P.ml - 1)) 1] s.mem t.mem := by
      rw [m]; exact frame_byte P.scr _ _ (Nat.le_refl _) (by omega) (by oomega)
    refine ⟨⟨⟨ctxW hg hc fr (fun r hr => .inl ⟨oEm + (P.K - P.ml - 1), 1, by oomega,
      by simpa using hr⟩) rd wr sp, hi, hf'⟩,
      fun i hi' => ?_⟩, by rw [t0, show oEm + (P.K - P.ml - 1) + 1 = oEm + (P.K - P.ml) by oomega], t1, tl, z⟩
    rw [emV, m, sa_write P.scr _ _ (by oomega) (by oomega)]
    by_cases e : i = P.K - P.ml - 1
    · rw [ite_eq_left (by omega)]; exact (ite_eq_left e).symm
    · rw [ite_eq_right (by omega)]; exact (he i hi').trans (ite_eq_right e).symm

/-- The message at the end of `EM`, if it is not empty. -/
theorem em6_vp (P : EP) :
    VP (fun σ s => (E0 h P σ s ∧ EMv P s.mem (e4 h P σ)) ∧
        s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + (P.K - P.ml)) ∧ s.gpr .r1 = P.msg ∧
        s.gpr .lr = BitVec.ofNat 32 P.ml ∧ s.z = decide (P.ml = 0))
      (.ite .eq (.block []) Impl.Bignum.Arm.copyBytes)
      (fun σ s => E0 h P σ s ∧ EMv P s.mem (e5 h P σ)) := by
  by_cases hP : ∃ σ, In h.H.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.1.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hi₀.k1024
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s hs => hf hs.1.1.2.2
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  refine VP.ite (fun _ _ _ _ h₁ h₂ => by rw [VG.Proof.X25519.Arm.eval_eq, VG.Proof.X25519.Arm.eval_eq, h₁.2.2.2.2,
      h₂.2.2.2.2]) (VP.block_nil fun σ s ⟨⟨⟨hc, he⟩, _, _, _, z⟩, e⟩ => ⟨hc, fun i hi => ?_⟩) ?_
  · have h0 : P.ml = 0 := by rw [VG.Proof.X25519.Arm.eval_eq, z] at e; simpa using e
    rw [he i hi]; exact (ite_eq_right (by omega)).symm
  by_cases h0 : P.ml = 0
  · exact VP.empty fun σ s ⟨⟨_, _, _, _, z⟩, e⟩ => by
      rw [VG.Proof.X25519.Arm.eval_eq, z, decide_eq_true h0] at e; exact absurd e (by decide)
  have hm := hi₀.ok.fits P.MSG (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hm
  have hmsg : RBuf (P.lay h.H.D) P.msg P.ml := ⟨hm, hi₀.ml32, ⟨P.MSG, by simp, Region.contains_self _ _⟩⟩
  refine (copy_vp (hg.wbuf (o := oEm + (P.K - P.ml)) (n := P.ml) (by oomega) (by omega)) hmsg
    (by rw [hg.addr (by oomega)]; exact (hg.ro ok (by oomega) (R := P.MSG) (by simp)).symm)
    (by omega) (f := fun σ i => (msgB P σ).getD i 0)
    (Inv := fun σ m => K0 h P σ ∧ ∀ i < P.K, i < P.K - P.ml → emV P.scr m i = e4 h P σ i)
    fun σ m m' ⟨k, ho⟩ hf' => ?_).mono
    (fun σ s ⟨⟨⟨⟨hc, hi, hf'⟩, he⟩, r0, r1, lr, _⟩, _⟩ => ⟨hc, ⟨⟨hi, hf'⟩, fun i hi _ => he i hi⟩, r0, r1, lr,
      fun i hi => ?_⟩) fun σ s ⟨hc, ⟨k, ho⟩, hs⟩ => ⟨⟨hc, k⟩, fun i hi => ?_⟩
  · rw [hg.addr (by oomega)] at hf'
    refine ⟨k, fun i hi hr => ?_⟩
    rw [emV, ← ho i hi hr]
    exact hf' _ fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by oomega) (by oomega) (by oomega) _
        (Region.contains_self _ _)
  · have e := (hc.st.ro (R := P.MSG) (by simp))
    have e2 := congrArg (fun l => l.getD i 0) e
    simp only [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some] at e2
    simp only [msgB, Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some, byteAt]
    exact e2
  · simp only [e5]
    by_cases hr : P.K - P.ml ≤ i ∧ i < P.K
    · rw [ite_eq_left hr, emV, show oEm + i = oEm + (P.K - P.ml) + (i - (P.K - P.ml)) by oomega,
        ← hg.byteAt_scr (by oomega)]
      exact hs _ (by omega)
    · rw [ite_eq_right hr]; exact ho i hi (by omega)

/-! ## `EM` -/

theorem e5_emAt {P : EP} {σ : State} (hf : fits h P) {m : Mem} (he : EMv P m (e5 h P σ)) :
    Proof.RsaOaep.EmAt (emV P.scr m) P.K h.H.D (seedB h P σ) (lhB h P σ) (msgB P σ) P.ml := by
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_, fun i h1 h2 => ?_, ?_, fun i hi => ?_⟩
  · rw [he 0 (by omega)]; simp only [e5, e4, e3, e2]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [he _ (by omega)]; simp only [e5, e4, e3, e2]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      Nat.add_sub_cancel_left]
  · rw [he _ (by omega)]; simp only [e5, e4, e3]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      show 1 + h.H.D + i - (1 + h.H.D) = i by omega]
  · rw [he _ (by omega)]; simp only [e5, e4, e3, e2]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [he _ (by omega)]; simp only [e5, e4]
    rw [ite_eq_right (by omega)]; exact ite_eq_left trivial
  · rw [he _ (by omega)]; simp only [e5]
    rw [ite_eq_left (by omega), show P.K - P.ml + i - (P.K - P.ml) = i by omega]

/-- `EM` before masking, from the checks' state when the message fits. -/
theorem em_vp (P : EP) :
    VP (E0 h P) (encEm h.H)
      (fun σ s => E0 h P σ s ∧ Proof.RsaOaep.EmAt (emV P.scr s.mem) P.K h.H.D (seedB h P σ) (lhB h P σ)
        (msgB P σ) P.ml) := by
  show VP _ (.seq (.block clrEm) (.seq Impl.Bignum.Arm.maskBytes (.seq (.block (seedSet h.H))
    (.seq Impl.Bignum.Arm.copyBytes (.seq (hashLabel h.H 6 oDig) (.seq (.block (lhSet h.H))
      (.seq Impl.Bignum.Arm.copyBytes (.seq (.block msgPos) (.seq (.block put1)
        (.ite .eq (.block []) Impl.Bignum.Arm.copyBytes)))))))))) _
  exact VP.assoc (VP.seq (em1_vp h P) (VP.assoc (VP.seq (em2_vp h P) (VP.seq (em3_vp h P)
    (VP.assoc (VP.seq (em4_vp h P) (VP.assoc (VP.seq (em5_vp h P) ((em6_vp h P).mono (fun _ _ h => h)
      fun σ s ⟨he0, he⟩ => ⟨he0, e5_emAt h he0.2.2 he⟩)))))))))

/-! ## `EM` masked -/

/-- `EM` masked, as the specification has it. -/
abbrev emB (g : OHash) (P : EP) (σ : State) : List Byte :=
  Proof.RsaOaep.emOf g.G h.H.D P.K P.ml (seedB h P σ) (lhB h P σ) (msgB P σ)

/-- A state of the body with `EM` masked at `scratch + oEm`. -/
abbrev E1 (g : OHash) (P : EP) (σ s : State) : Prop :=
  E0 h P σ s ∧ ∀ i < P.K, emV P.scr s.mem i = (emB h g P σ).getD i 0

end VG.Proof.RsaOaep.Arm.Enc
