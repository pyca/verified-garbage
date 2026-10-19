module

public import VerifiedGarbage.Proof.RsaPss.Arm.SgEnc2
public import VerifiedGarbage.Proof.RsaPss.EncBytes
import all Init.Data.Nat.Bitwise.Basic
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
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.RsaPss.Arm.CtInit
import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
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
# RSASSA-PSS signing on ARMv7: `maskedDB`, and `EM`

`DB ⊕= MGF1(H, dbLen)` (`mask_vp`), `maskedDB`'s first byte ANDed with the
mask `c` (`top_vp`): `EM` is `emT` of the specification's encoding
(`EncBytes.lean`), and so is the whole encoding (`enc_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Sg

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h : PssHash)

/-- `EM`'s bytes outside `DB` and `H`: the leading zero and `0xbc`. -/
abbrev Ko (P : EP) (σ : State) (m : Mem) : Prop :=
  Kp h P σ m ∧ (∀ i < lo P, m (sa P.scr (oEm + i)) = 0) ∧ m (sa P.scr (oEm + (P.K - 1))) = 0xbc

/-- The mask. -/
abbrev mkS (P : EP) (σ : State) : List Byte := Spec.Mgf1.mgf1 h.G (Hs h P σ) (dbN h P)

theorem Hs_length (P : EP) (σ : State) : (Hs h P σ).length = h.D := by
  rw [Hs, ← h.hash]; have := (PssHash.valid h).2 (Mp h P σ); rw [this, h.glen]

/-- `maskedDB`, before its first byte's top bits are cleared. -/
theorem mask_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emC h P σ)) (mgfXor h.H)
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ko h P σ s.mem ∧
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = dbv h P σ i ^^^ (mkS h P σ).getD i 0) ∧
        ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (Hs h P σ).getD i 0) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.1.2.1
  have hK := hi₀.k1024
  have hlo : lo P ≤ 1 := by unfold lo; split <;> omega
  have hdb : P.sl + 1 ≤ dbN h P := by unfold dbN; have := hf.2; omega
  have hsum : lo P + dbN h P + h.D + 1 = P.K := by unfold dbN; have := hf.2; omega
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega
  have hB := h.B_le
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 2048 := rfl
  have fit := hg.fit
  -- What `mgfXor` writes misses the parameters and the bytes of `EM` outside `DB` and `H`.
  have away : ∀ r ∈ mgfW h (P.lay h.D) P.scr (lo P) (dbN h P), Away3 (P.lay h.D) r ∧
      ∀ i, (i < lo P ∨ i = P.K - 1) → ¬ r.Contains (sa P.scr (oEm + i)) 1 := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · refine ⟨away3_ctW h hg (by omega) r hr, fun i hi => ?_⟩
      exact ctW_em h hg (T := h.B) (o := oEm + i) (n := 1) (by omega) (by omega) (by omega) r hr _
        (Region.contains_self _ _)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨away3_scr hg (by omega), fun i hi => Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by omega)
          (by omega) (by omega) _ (Region.contains_self _ _)⟩
      all_goals exact ⟨away3_slot (by decide) (by decide), fun i hi => (hg.slot ok (o := oEm + i) (n := 1) (by omega)
        (by rw [hg.F]; decide)).symm _ (Region.contains_self _ _)⟩
  have mp : MP h (P.lay h.D) P.scr (lo P) (dbN h P) (Hs h P) (Ko h P) := by
    refine ⟨hg, by omega, by omega, Hs_length h P, fun σ m m' ⟨hk, h0, hbc⟩ hf' => ⟨hk.keep h hf' fun r hr =>
      (away r hr).1, fun i hi => ?_, ?_⟩, fun σ m hk => hk.1.2.2.2.1, fun σ m hk => hk.1.2.2.2.2⟩
    · rw [← h0 i hi]; exact hf' _ fun r hr => (away r hr).2 i (.inl hi)
    · rw [← hbc]; exact hf' _ fun r hr => (away r hr).2 _ (.inr rfl)
  refine (mgf_vp h mp (dbv := dbv h P)).mono (fun σ s ⟨hc, hk, he⟩ => ⟨hc, ⟨hk.1, fun i hi => ?_, ?_⟩, fun i hi => ?_,
    fun i hi => ?_⟩) fun σ s h => h
  · rw [he i (by omega)]
    unfold emC emB emA
    rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left hi]
  · rw [he _ (by omega)]
    exact ite_eq_left rfl
  · rw [Nat.add_assoc, he _ (by omega)]
    unfold emC emB emA
    rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      Nat.add_sub_cancel_left]
  · rw [Nat.add_assoc, Nat.add_assoc, he _ (by omega)]
    unfold emC emB
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
    congr 1; omega

/-- `EM`, as the specification encodes it (`RsaPss.emT`). -/
abbrev emF (P : EP) (σ : State) (i : Nat) : Byte :=
  RsaPss.emT (lo P) (dbN h P) P.sl (saltB P σ) (Hs h P σ) (mkS h P σ) ((cW (xB P)).setWidth 8) i

theorem andByte (b : Byte) (w : BitVec 32) : (b.setWidth 32 &&& w).setWidth 8 = b &&& w.setWidth 8 := by
  have e1 : (b.setWidth 32).setWidth 8 = b := by simp
  rw [BitVec.setWidth_and, e1]

theorem topAnd_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0])
    (.block topAnd) hc).isSome = true := ⟨_, by taint_decide⟩

/-- `maskedDB`'s first byte ANDed with the mask: `EM`. -/
theorem top_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ko h P σ s.mem ∧
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = dbv h P σ i ^^^ (mkS h P σ).getD i 0) ∧
        ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (Hs h P σ).getD i 0)
      (.seq (.block topSet) (.block topAnd))
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Kp h P σ s.mem ∧ EMv P s.mem (emF h P σ)) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.1.2.1
  have hK := hi₀.k1024
  have hlo : lo P ≤ 1 := by unfold lo; split <;> omega
  have hdb : P.sl + 1 ≤ dbN h P := by unfold dbN; have := hf.2; omega
  have hsum : lo P + dbN h P + h.D + 1 = P.K := by unfold dbN; have := hf.2; omega
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 2048 := rfl
  have fit := hg.fit
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ko h P σ s.mem ∧
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = dbv h P σ i ^^^ (mkS h P σ).getD i 0) ∧
        ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (Hs h P σ).getD i 0) ∧
      s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P) ∧ s.gpr .r1 = cW (xB P))
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hk, hd, hh⟩ => ?_)
    (VP.taint _ topAnd_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨⟨hc, hk, hd, hh⟩, r0, r1⟩ => ?_)
  · have hw : WP isa (.block topSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P) ∧ t.gpr .r1 = cW (xB P) := by
      prun [topSet, atDb, atS, addSlot, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, hk.1.2.2.1,
        hk.1.2.2.2.1, movw_val (show oEm < 2 ^ 16 by decide), BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hk, m ▸ hd, m ▸ hh⟩, r0, r1⟩
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]
  · have ad : State.addr (P.scr + BitVec.ofNat 32 (oEm + lo P)) = sa P.scr (oEm + lo P) := hg.addr (by omega)
    have rd : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + lo P)) 1 := hg.rd hc.st (by omega)
    have wd : InRegions s.wr (sa P.scr (oEm + lo P)) 1 := hg.wr hc.st (by omega)
    have hw : WP isa (.block topAnd) s fun t =>
        t.mem = s.mem.writeW (sa P.scr (oEm + lo P)) (s.mem (sa P.scr (oEm + lo P)) &&& (cW (xB P)).setWidth 8) ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
      prun [topAnd, r0, r1, ad, rd, wd, dpVal, andByte]
    refine WP.mono hw fun t ⟨m, rd', wr', sp'⟩ => ?_
    have fr : Frame [sR P.scr (oEm + lo P) 1] s.mem t.mem := by
      rw [m]; exact frame_byte P.scr _ _ (Nat.le_refl _) (by omega) (by omega)
    refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd' wr' sp', hk.1.keep h fr fun r hr => ?_, fun i hi => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by omega)
    · simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by omega) (by rw [hg.F]; decide)
    · simp only [List.mem_singleton] at hr; subst hr; exact away3_scr hg (by omega)
    rw [m, sa_write P.scr _ _ (by omega) (by omega)]
    have hl := Hs_length h P σ
    unfold emF RsaPss.emT
    by_cases h1 : i < lo P
    · rw [ite_eq_right (by omega), ite_eq_left h1]; exact hk.2.1 i h1
    rw [ite_eq_right h1]
    by_cases h2 : i - lo P < dbN h P
    · rw [ite_eq_left h2]
      by_cases h3 : i - lo P = 0
      · rw [ite_eq_left (by omega), ite_eq_left h3, show oEm + lo P = oEm + lo P + 0 from rfl, hd 0 (by omega), h3]
      · rw [ite_eq_right (by omega), ite_eq_right h3, show oEm + i = oEm + lo P + (i - lo P) by omega, hd _ h2]
    rw [ite_eq_right h2, ite_eq_right (by omega)]
    by_cases h4 : i - lo P < dbN h P + (Hs h P σ).length
    · rw [ite_eq_left h4, show oEm + i = oEm + lo P + dbN h P + (i - lo P - dbN h P) by omega, hh _ (by omega)]
    · rw [ite_eq_right h4, show oEm + i = oEm + (P.K - 1) by omega]; exact hk.2.2

/-- The encoding, when everything fits. -/
theorem enc_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (E0 h P) (signEnc h.H)
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Kp h P σ s.mem ∧ EMv P s.mem (emF h P σ)) := by
  show VP _ (.seq (yDig h.H 16) (.seq (.block (cpSalt h.H)) (.seq (.ite .eq (.block []) Impl.Bignum.Arm.copyBytes)
    (.seq (.block (lenSet h.H 18)) (.seq (ctHash h.H) (.seq (.block clrEm) (.seq Impl.Bignum.Arm.maskBytes
    (.seq (.block saltPos) (.seq (.block put1) (.seq (.ite .eq (.block []) Impl.Bignum.Arm.copyBytes)
    (.seq (.block (putH h.H)) (.seq Impl.Bignum.Arm.copyBytes (.seq (.block bcSet) (.seq (.block bcPut)
    (.seq (mgfXor h.H) (.seq (.block topSet) (.block topAnd))))))))))))))))) _
  exact (yDig_sg h P hP).seq (VP.assoc ((salt_vp h P hP).seq ((lenSet_vp h P).seq ((hash_vp h P hP).seq
    (VP.assoc ((clr_vp h P hP).seq (VP.assoc ((one_vp h P hP).seq ((cpS_vp h P hP).seq
    (VP.assoc ((putH_vp h P hP).seq (VP.assoc ((bc_vp h P hP).seq ((mask_vp h P hP).seq (top_vp h P hP)))))))))))))))

end VG.Proof.RsaPss.Arm.Sg
