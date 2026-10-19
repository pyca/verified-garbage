module
public import VerifiedGarbage.Proof.RsaPss.Arm.CtHash
public import VerifiedGarbage.Proof.RsaPss.Arm.CtSel
public import VerifiedGarbage.Proof.Mgf1.Basic

import VerifiedGarbage.Proof.RsaPss.Arm.CtXor
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
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
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.RsaPss.Arm.CtInit
import VerifiedGarbage.Proof.RsaPss.Arm.CtPad
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Sha256.StateMem
import VerifiedGarbage.Spec.Pbkdf2.Generic

/-!
# RSASSA-PSS on ARMv7: `DB ⊕= MGF1(H, dbLen)`

`mgf_vp`: with `DB` at `oEm + lo` (`dbLen` bytes, both in their slots) and
the seed `H` after it, `mgfXor` XORs MGF1's mask of `H` into `DB`, one
digest of `H ‖ C` (hashed by `ctHash` in one block) at a time.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)
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
  Lay.fr_sep h (by unfold frameBytes at hd; omega) (by unfold frameBytes at he; omega)

/-- A slot other than `sBi` misses what `ctHash` writes. -/
theorem ctW_slot (hg : Geo L scr) {T : Nat} (hT : T ≤ 2048) {d : Nat} (hd : d + 4 ≤ frameBytes)
    (hb : d + 4 ≤ sBi ∨ sBi + 4 ≤ d) : ∀ r ∈ ctW h L scr T, (slotR L d).Disjoint r := by
  have hN := h.N_le
  have hB := h.B_le
  have hso := h.so_le
  obtain ⟨σ', ok⟩ := hg.ok
  have hF : d + 4 ≤ L.F + 56 := by rw [hg.F]; unfold frameBytes at hd ⊢; omega
  have hC : L.C ≤ 2 ^ 32 := by have := ok.B56; have := L.B.isLt; omega
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hg.slot ok (by pomega) hF
  · exact Lay.fr_low (by unfold frameBytes at hd; omega) hC
  · exact hg.slot ok (by pomega) hF
  · exact hg.slot ok (by pomega) hF
  · exact hg.slot ok (by pomega) hF
  · exact hg.slot ok (by pomega) hF
  · exact hg.slot ok (by pomega) hF
  · exact slotSep hd (by decide) hb
  · exact hg.slot ok (by pomega) hF

/-- A range of `EM`'s place misses what `ctHash` writes. -/
theorem ctW_em (hg : Geo L scr) {T : Nat} (hT : T ≤ 2048) {o n : Nat} (h₁ : oEm ≤ o) (h₂ : o + n ≤ oY) :
    ∀ r ∈ ctW h L scr T, (sR scr o n).Disjoint r := by
  have hN := h.N_le
  have hB := h.B_le
  have hso := h.so_le
  obtain ⟨σ', ok⟩ := hg.ok
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Geo.sep (by pomega) (by pomega) (by pomega)
  · exact hg.low ok (by pomega)
  · exact Geo.sep (by pomega) (by pomega) (by pomega)
  · exact Geo.sep (by pomega) (by pomega) (by pomega)
  · exact Geo.sep (by pomega) (by pomega) (by pomega)
  · exact Geo.sep (by pomega) (by pomega) (by pomega)
  · exact Geo.sep (by pomega) (by pomega) (by pomega)
  · exact (hg.slot ok (by pomega) (by rw [hg.F]; decide)).symm
  · exact Geo.sep (by pomega) (by pomega) (by pomega)

/-- What `mgfXor` writes. -/
abbrev mgfW (L : Lay) (scr : BitVec 32) (lo db : Nat) : List Region :=
  ctW h L scr h.B ++ [sR scr (oEm + lo) db, slotR L sCtr, slotR L sDone, slotR L sL, slotR L sNb]

/-- The memory before iteration `c` of `mgfXor`: the counter, the bytes
masked, `DB` masked up to `c hLen` bytes, and the seed. -/
structure MB (L : Lay) (scr : BitVec 32) (lo db c : Nat) (dbv : Nat → Byte) (seed : List Byte) (m : Mem) : Prop where
  ctr : m.readW (L.fr sCtr) 32 = BitVec.ofNat 32 c
  done : m.readW (L.fr sDone) 32 = BitVec.ofNat 32 (c * h.D)
  dbx : ∀ i < db, m (sa scr (oEm + lo + i)) =
    if i < c * h.D then dbv i ^^^ (Spec.Mgf1.mgf1 h.G seed db).getD i 0 else dbv i
  sd : ∀ i < h.D, m (sa scr (oEm + lo + db + i)) = seed.getD i 0

theorem MB.keep {lo db c : Nat} {dbv : Nat → Byte} {seed : List Byte} {m m' : Mem} {rs : List Region}
    (hm : MB h L scr lo db c dbv seed m) (hf : Frame rs m m') (hn : oEm + lo + db + h.D < 2 ^ 64)
    (hs : ∀ r ∈ rs, (slotR L sCtr).Disjoint r ∧ (slotR L sDone).Disjoint r ∧
      (sR scr (oEm + lo) db).Disjoint r ∧ (sR scr (oEm + lo + db) h.D).Disjoint r) :
    MB h L scr lo db c dbv seed m' :=
  ⟨slot_keep hf (fun r hr => (hs r hr).1) hm.ctr, slot_keep hf (fun r hr => (hs r hr).2.1) hm.done,
    sbytes_keep hf (fun r hr => (hs r hr).2.2.1) (by omega) hm.dbx,
    sbytes_keep hf (fun r hr => (hs r hr).2.2.2) (by omega) hm.sd⟩

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
  Mem.readW_writeW_sep (Offset.sep _ h (by unfold frameBytes at hd; omega) (by unfold frameBytes at he; omega))
    (by decide)

/-! ## The parameters and the stages of an iteration -/

/-- The parameters of `mgfXor`: `DB` at `oEm + lo` (`db` bytes) and the seed
after it, fitting before `Y`; and what the caller keeps (`Inv`), with the
slots of `lo` and `db`. -/
structure MP (L : Lay) (scr : BitVec 32) (lo db : Nat) (seed : State → List Byte)
    (Inv : State → Mem → Prop) : Prop where
  hg : Geo L scr
  db0 : 0 < db
  fit : lo + db + h.D ≤ 1024
  sd : ∀ σ, (seed σ).length = h.D
  I : ∀ σ m m', Inv σ m → Frame (mgfW h L scr lo db) m m' → Inv σ m'
  lo : ∀ σ m, Inv σ m → m.readW (L.fr sLo) 32 = BitVec.ofNat 32 lo
  dbs : ∀ σ m, Inv σ m → m.readW (L.fr sDb) 32 = BitVec.ofNat 32 db

variable {lo db : Nat} {seed : State → List Byte} {Inv : State → Mem → Prop} {dbv : State → Nat → Byte}

/-- What the caller keeps, and the memory before iteration `c`. -/
abbrev MI (L : Lay) (scr : BitVec 32) (lo db c : Nat) (dbv : State → Nat → Byte) (seed : State → List Byte)
    (Inv : State → Mem → Prop) (σ : State) (m : Mem) : Prop :=
  Inv σ m ∧ MB h L scr lo db c (dbv σ) (seed σ) m

/-- What misses the slots of the counter and of the bytes masked, `DB` and the seed. -/
abbrev Away (L : Lay) (scr : BitVec 32) (lo db : Nat) (r : Region) : Prop :=
  (slotR L sCtr).Disjoint r ∧ (slotR L sDone).Disjoint r ∧ (sR scr (oEm + lo) db).Disjoint r ∧
    (sR scr (oEm + lo + db) h.D).Disjoint r

theorem MP.keep (P : MP h L scr lo db seed Inv) {c : Nat} {σ : State} {m m' : Mem} {rs : List Region}
    (hm : MI h L scr lo db c dbv seed Inv σ m) (hf : Frame rs m m') (hsub : ∀ r ∈ rs, r ∈ mgfW h L scr lo db)
    (hs : ∀ r ∈ rs, Away h L scr lo db r) : MI h L scr lo db c dbv seed Inv σ m' :=
  ⟨P.I σ m m' hm.1 (hf.mono hsub), hm.2.keep h hf (by have := P.fit; unfold oEm; omega) hs⟩

/-- What `ctHash` writes misses them. -/
theorem MP.ctW_away (P : MP h L scr lo db seed Inv) : ∀ r ∈ ctW h L scr h.B, Away h L scr lo db r := by
  have := P.fit
  have := h.B_le
  intro r hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ctW_slot h P.hg (by omega) (d := sCtr) (by decide) (by decide) r hr
  · exact ctW_slot h P.hg (by omega) (d := sDone) (by decide) (by decide) r hr
  · exact ctW_em h P.hg (by omega) (o := oEm + lo) (n := db) (Nat.le_add_right _ _) (by pomega) r hr
  · exact ctW_em h P.hg (by omega) (o := oEm + lo + db) (n := h.D) (by pomega) (by pomega) r hr

/-- So does a slot other than theirs. -/
theorem MP.slot_away (P : MP h L scr lo db seed Inv) {d : Nat} (hd : d + 4 ≤ frameBytes)
    (h₁ : d + 4 ≤ sCtr ∨ sDone + 4 ≤ d) : Away h L scr lo db (slotR L d) := by
  have := P.fit
  obtain ⟨σ', ok⟩ := P.hg.ok
  have hF : d + 4 ≤ L.F + 56 := by rw [P.hg.F]; unfold frameBytes at hd ⊢; omega
  refine ⟨slotSep (by decide) hd (by unfold sCtr sDone at *; omega), slotSep (by decide) hd (by unfold sCtr sDone at *; omega),
    (P.hg.slot ok (by pomega) hF).symm, (P.hg.slot ok (by pomega) hF).symm⟩

/-- `Y`'s first block, zero. -/
abbrev Yz (scr : BitVec 32) (m : Mem) : Prop := ∀ i < h.B, m (sa scr (oY + i)) = 0

/-- `Y`'s first block: the seed, then zeros. -/
abbrev Ys (scr : BitVec 32) (sd : List Byte) (m : Mem) : Prop :=
  ∀ i < h.B, m (sa scr (oY + i)) = if i < h.D then sd.getD i 0 else 0

/-- The first block cleared. -/
theorem mgfA_vp (P : MP h L scr lo db seed Inv) (c : Nat) :
    VP (fun σ s => Ctx L scr σ s ∧ MI h L scr lo db c dbv seed Inv σ s.mem)
      (.seq (.block (mgfClr h.H)) Impl.Bignum.Arm.maskBytes)
      (fun σ s => Ctx L scr σ s ∧ MI h L scr lo db c dbv seed Inv σ s.mem ∧ Yz h scr s.mem) := by
  have hB := h.B_le
  have hB64 := h.B_ge
  have hg := P.hg
  refine VP.seq (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm)
    fun σ s ⟨hc, hm⟩ => ?_) ((zero_vp (hg.wbuf (o := oY) (n := h.B) (by pomega) (by omega)) (by omega)
      (Inv := MI h L scr lo db c dbv seed Inv) fun σ m m' hm hf => P.keep h hm (by rwa [hg.addr (by pomega)] at hf) (by simp)
        fun r hr => P.ctW_away h r (by simp only [List.mem_singleton] at hr; subst hr; simp)).mono
      (fun _ _ h => h) fun σ s ⟨hc, hm, hz⟩ => ⟨hc, hm, fun i hi => by
        rw [← hg.byteAt_scr (by pomega)]; exact hz i hi⟩)
  have hw : WP isa (.block (mgfClr h.H)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ t.gpr .r0 = scr + BitVec.ofNat 32 oY ∧ t.gpr .r2 = 0 ∧ t.gpr .lr = BitVec.ofNat 32 h.B := by
    prun [mgfClr, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS,
      movw_val (show oY < 2 ^ 16 by decide), movw_val (show blk h.H < 2 ^ 16 by show h.B < 2 ^ 16; omega)]
  exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r2, lr⟩ => ⟨hc.regs rd wr sp m, m ▸ hm, r0, r2, lr⟩

/-- The seed to `Y`. -/
theorem mgfB_vp (P : MP h L scr lo db seed Inv) (c : Nat) :
    VP (fun σ s => Ctx L scr σ s ∧ MI h L scr lo db c dbv seed Inv σ s.mem ∧ Yz h scr s.mem)
      (.seq (.block (mgfSeed h.H)) Impl.Bignum.Arm.copyBytes)
      (fun σ s => Ctx L scr σ s ∧ MI h L scr lo db c dbv seed Inv σ s.mem ∧ Ys h scr (seed σ) s.mem) := by
  have hB := h.B_le
  have hB64 := h.B_ge
  have hD := h.D_le
  have hD0 := h.D_pos
  have hN := h.N_le
  have hNL := h.NL
  have hfit := P.fit
  have hg := P.hg
  -- `Y`'s bytes after the seed's place stay zero.
  let Z : State → Mem → Prop := fun σ m => MI h L scr lo db c dbv seed Inv σ m ∧
    ∀ i < h.B - h.D, m (sa scr (oY + h.D + i)) = 0
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ Z σ s.mem ∧ s.gpr .r0 = scr + BitVec.ofNat 32 oY ∧
      s.gpr .r1 = scr + BitVec.ofNat 32 (oEm + lo + db) ∧ s.gpr .lr = BitVec.ofNat 32 h.D ∧
      ∀ i < h.D, s.mem (byteAt (scr + BitVec.ofNat 32 (oEm + lo + db)) i) = (seed σ).getD i 0)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hm, hz⟩ => ?_)
    ((copy_vp (hg.wbuf (o := oY) (n := h.D) (by pomega) hD0) (hg.rbuf (o := oEm + lo + db) (n := h.D) (by pomega) hD0)
      (by rw [hg.addr (by pomega), hg.addr (by pomega)]; exact Geo.sep (by pomega) (by pomega) (by pomega)) hD0
      (Inv := Z) (f := fun σ i => (seed σ).getD i 0) fun σ m m' ⟨hm, hz⟩ hf => ?_).mono (fun _ _ h => h)
      fun σ s ⟨hc, ⟨hm, hz⟩, hy⟩ => ⟨hc, hm, fun i hi => ?_⟩)
  · have hw : WP isa (.block (mgfSeed h.H)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.sp = s.sp ∧ t.gpr .r0 = scr + BitVec.ofNat 32 oY ∧ t.gpr .r1 = scr + BitVec.ofNat 32 (oEm + lo + db) ∧
        t.gpr .lr = BitVec.ofNat 32 h.D := by
      prun [mgfSeed, atS, atDb, addSlot, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, P.lo σ _ hm.1,
        P.dbs σ _ hm.1, movw_val (show oY < 2 ^ 16 by decide), movw_val (show oEm < 2 ^ 16 by decide),
        movw_val (show dig h.H < 2 ^ 16 by show h.D < 2 ^ 16; omega), BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    refine WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr⟩ => ⟨hc.regs rd wr sp m, ⟨m ▸ hm, fun i hi => ?_⟩, r0, r1, lr,
      fun i hi => ?_⟩
    · rw [m, Nat.add_assoc]; exact hz _ (by omega)
    · rw [m, hg.byteAt_scr (by pomega)]; exact hm.2.sd i hi
  · rw [hg.addr (by pomega)] at hf
    refine ⟨P.keep h (rs := [sR scr oY h.B]) hm (Frame.sub hf fun r hr => ⟨sR scr oY h.B, by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (Nat.le_refl _) (by omega)⟩) (by simp)
      fun r hr => P.ctW_away h r (by simp only [List.mem_singleton] at hr; subst hr; simp), ?_⟩
    exact sbytes_keep hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by pomega) (by pomega) (by pomega)) (by pomega) hz
  · by_cases hi' : i < h.D
    · rw [ite_eq_left hi', ← hy i hi', hg.byteAt_scr (by pomega)]
    · rw [ite_eq_right hi', show oY + i = oY + h.D + (i - h.D) by omega]; exact hz _ (by omega)

/-- What `ctHash` keeps of an iteration: the memory before it, and the
slots of its message's length and blocks. -/
abbrev HI (L : Lay) (scr : BitVec 32) (lo db c : Nat) (dbv : State → Nat → Byte) (seed : State → List Byte)
    (Inv : State → Mem → Prop) (σ : State) (m : Mem) : Prop :=
  MI h L scr lo db c dbv seed Inv σ m ∧ m.readW (L.fr sL) 32 = BitVec.ofNat 32 (h.D + 4) ∧
    m.readW (L.fr sNb) 32 = BitVec.ofNat 32 1

theorem ctrPut_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1])
    (.block ctrPut) hc).isSome = true := ⟨_, by taint_decide⟩

theorem shr0 (c : Nat) : (BitVec.ofNat 32 c).setWidth 8 = BitVec.ofNat 8 (c / 256 ^ 0) := by
  rw [Nat.pow_zero, Nat.div_one]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- The counter after the seed in `Y`. -/
theorem mgfC_vp (P : MP h L scr lo db seed Inv) {c : Nat} (hc32 : c < 2 ^ 32) :
    VP (fun σ s => Ctx L scr σ s ∧ MI h L scr lo db c dbv seed Inv σ s.mem ∧ Ys h scr (seed σ) s.mem)
      (.seq (.block (ctrSet h.H)) (.block ctrPut))
      (fun σ s => Ctx L scr σ s ∧ HI h L scr lo db c dbv seed Inv σ s.mem ∧
        ∀ i < 1 * h.B, s.mem (sa scr (oY + i)) = (seed σ ++ Spec.Rsa.i2osp c 4).getD i 0) := by
  have hB := h.B_le
  have hB64 := h.B_ge
  have hD := h.D_le
  have hD0 := h.D_pos
  have hN := h.N_le
  have hNL := h.NL
  have hone := h.one
  have hfit := P.fit
  have hg := P.hg
  obtain ⟨σ', ok⟩ := hg.ok
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ (HI h L scr lo db c dbv seed Inv σ s.mem ∧ Ys h scr (seed σ) s.mem) ∧
      s.gpr .r0 = scr + BitVec.ofNat 32 (oY + h.D) ∧ s.gpr .r1 = BitVec.ofNat 32 c)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hm, hy⟩ => ?_)
    (VP.taint _ ctrPut_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hc, ⟨hm, hy⟩, r0, r1⟩ => ?_)
  · have hw : WP isa (.block (ctrSet h.H)) s fun t =>
        t.mem = (s.mem.writeW (L.fr sL) (BitVec.ofNat 32 (h.D + 4))).writeW (L.fr sNb) (BitVec.ofNat 32 1) ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr .r0 = scr + BitVec.ofNat 32 (oY + h.D) ∧
        t.gpr .r1 = BitVec.ofNat 32 c := by
      prun [ctrSet, atS, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.wFr hg, hc.slotS, hm.2.ctr,
        movw_val (show oY + dig h.H < 2 ^ 16 by show oY + h.D < 2 ^ 16; pomega),
        movw_val (show dig h.H + 4 < 2 ^ 16 by show h.D + 4 < 2 ^ 16; omega), movw_val (show 1 < 2 ^ 16 by decide)]
    refine WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1⟩ => ?_
    have fr : Frame [slotR L sL, slotR L sNb] s.mem t.mem := by
      rw [m]
      exact (slot_frame L _ _ _).mono (by simp) |>.trans ((slot_frame L _ _ _).mono (by simp))
    have hs : ∀ r ∈ [slotR L sL, slotR L sNb], Away h L scr lo db r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact P.slot_away h (by decide) (by decide)
      · exact P.slot_away h (by decide) (by decide)
    refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp,
      ⟨⟨P.keep h hm fr (by simp) hs, ?_, ?_⟩, sbytes_keep fr (fun r hr => ?_) (by pomega) hy⟩, r0, r1⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact slotW hg (by decide)
      · exact slotW hg (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact slotSep (by decide) (by decide) (by decide)
      · exact slotSep (by decide) (by decide) (by decide)
    · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
    · rw [m, Mem.readW_writeW_self32]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hg.slot ok (by pomega) (by rw [hg.F]; decide)).symm
      · exact (hg.slot ok (by pomega) (by rw [hg.F]; decide)).symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
  · have a0 : State.addr (scr + BitVec.ofNat 32 (oY + h.D)) = sa scr (oY + h.D) := hg.addr (by pomega)
    have aj : ∀ j, j < 4 → State.addr (scr + BitVec.ofNat 32 (oY + h.D + j)) = sa scr (oY + h.D + j) :=
      fun j hj => hg.addr (by pomega)
    have wj : ∀ j, j < 4 → InRegions s.wr (sa scr (oY + h.D + j)) 1 := fun j hj => hg.wr hc.st (by pomega)
    have w0 : InRegions s.wr (sa scr (oY + h.D)) 1 := hg.wr hc.st (by pomega)
    have hw : WP isa (.block ctrPut) s fun t =>
        t.mem = (((s.mem.writeW (sa scr (oY + h.D)) (BitVec.ofNat 8 (c / 256 ^ 3))).writeW (sa scr (oY + h.D + 1))
          (BitVec.ofNat 8 (c / 256 ^ 2))).writeW (sa scr (oY + h.D + 2)) (BitVec.ofNat 8 (c / 256 ^ 1))).writeW
            (sa scr (oY + h.D + 3)) (BitVec.ofNat 8 (c / 256 ^ 0)) ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
      prun [ctrPut, r0, r1, a0, aj 1 (by decide), aj 2 (by decide), aj 3 (by decide), w0, wj 1 (by decide),
        wj 2 (by decide), wj 3 (by decide), shrByte hc32 3, shrByte hc32 2, shrByte hc32 1, shr0 c,
        BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
    have fr : Frame [sR scr oY h.B] s.mem t.mem := by
      rw [m]
      refine (((frame_byte scr _ _ ?_ ?_ ?_).trans (frame_byte scr _ _ ?_ ?_ ?_)).trans
        (frame_byte scr _ _ ?_ ?_ ?_)).trans (frame_byte scr _ _ ?_ ?_ ?_) <;> pomega
    refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp,
      ⟨P.keep h hm.1 fr (by simp) fun r hr => P.ctW_away h r (by
        simp only [List.mem_singleton] at hr; subst hr; simp),
        by rw [← hm.2.1]; exact slot_keep fr (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by pomega) (by rw [hg.F]; decide)) rfl,
        by rw [← hm.2.2]; exact slot_keep fr (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by pomega) (by rw [hg.F]; decide)) rfl⟩,
      fun i hi => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by pomega)
    · simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by pomega) (by rw [hg.F]; decide)
    rw [Nat.one_mul] at hi
    rw [m, sa_write scr _ _ (o := oY + h.D + 3) (i := oY + i) (by pomega) (by pomega),
      sa_write scr _ _ (o := oY + h.D + 2) (i := oY + i) (by pomega) (by pomega),
      sa_write scr _ _ (o := oY + h.D + 1) (i := oY + i) (by pomega) (by pomega),
      sa_write scr _ _ (o := oY + h.D) (i := oY + i) (by pomega) (by pomega), RsaPss.getD_app, P.sd σ, hy i hi]
    by_cases h1 : i < h.D
    · simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]
    by_cases h2 : i < h.D + 4
    · obtain ⟨j, rfl⟩ : ∃ j, i = h.D + j := ⟨i - h.D, by omega⟩
      rw [Nat.add_sub_cancel_left, i2osp4_getD c _ (by omega)]
      have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;>
        simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right, Nat.reduceSub]
    · rw [getD_ge (l := Spec.Rsa.i2osp c 4) (i := i - h.D) (by rw [i2osp4_length]; omega)]
      simp (disch := omega) only [↓ite_eq_right]

end VG.Proof.RsaPss.Arm
