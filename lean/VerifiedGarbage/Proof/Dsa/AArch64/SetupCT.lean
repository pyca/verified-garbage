module

import VerifiedGarbage.Proof.Dsa.AArch64.Setup
meta import VerifiedGarbage.Proof.Dsa.AArch64.Setup
public import VerifiedGarbage.Proof.Dsa.AArch64.ProductCT
public import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Dsa.AArch64.ProductCT
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.Arithmetic
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Spec.Dsa
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Double
meta import VerifiedGarbage.Proof.Bignum.AArch64.Mont
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Bignum.AArch64.Setup
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.Store
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Dsa.AArch64.Arithmetic
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Spec.Dsa

/-! # Constant-time Montgomery constants for padded DSA moduli -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- The count and index used to initialize a constant are public. -/
def SmallHead (L : Lay) (s : State) : Prop :=
  GoodL L s ∧ s.gpr .x12 = BitVec.ofNat 64 L.w ∧ s.gpr .x13 = 0

/-- Clearing an array and setting its low word has no value-dependent trace. -/
theorem small_ct {a : Nat} (ha : a < 8)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block [ldh .x8 (sArr a), movi .x7 0]) hc).isSome = true) :
    RelCT isa (Two GoodL) (Arithmetic.small a 1) (fun _ _ => True) := by
  unfold Arithmetic.small
  refine RelCT.seq (two_piece (Ψ := SmallHead) [.x0] pins_good (by taint_decide) ?_) ?_
  · intro L s hg
    refine WP.mono (WP.keep [.x12, .x9, .x13] (Q := fun t =>
      t.gpr .x12 = BitVec.ofNat 64 L.w ∧ t.gpr .x13 = 0 ∧ t.mem = s.mem) ?_ rfl rfl rfl)
      fun t ⟨⟨h12, hcx, hm⟩, hk⟩ =>
        ⟨⟨⟨hg.1.scr.congr hk.wr, (hk.gpr .x0 (by decide)).trans hg.1.x0, hm ▸ hg.1.hdr⟩, hg.2⟩, h12, hcx⟩
    brun [hg.1.x0, hdr_enc (show sW < 32 by decide), hg.1.hdr.hw,
      hg.1.scr.ld (show 8 * sW + 8 ≤ L.Z by have := hdr_lt_slot L.w 8 (show sW < 32 by decide); have := hg.2; omega)]
  rw [setWord_eq]
  refine RelCT.seq (two_piece (Ψ := fun L t => t.gpr .x8 = off L.B (slot L.w a) ∧
    t.gpr .x12 = BitVec.ofNat 64 L.w ∧ t.gpr .x13 = 0 ∧ t.gpr .x7 = 0) [.x0]
    (fun L s t hs ht => pins_good L s t hs.1 ht.1) hT ?_)
    (two_taint [.x8, .x12, .x13, .x7] (fun L s t hs ht r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.2.2.1.trans ht.2.2.1.symm
      · exact hs.2.2.2.trans ht.2.2.2.symm) (by taint_decide))
  intro L s ⟨hg, h12, hcx⟩
  refine WP.mono (WP.keep [.x8, .x7] (Q := fun t => t.gpr .x8 = off L.B (slot L.w a) ∧ t.gpr .x7 = 0) ?_ rfl rfl rfl)
    fun t ⟨⟨h8, h7⟩, hk⟩ => ⟨h8, (hk.gpr .x12 (by decide)).trans h12, (hk.gpr .x13 (by decide)).trans hcx, h7⟩
  brun [hg.1.x0, hdr_enc (show sArr a < 32 by unfold sArr; omega), hg.1.hdr.harr a ha,
    hg.1.scr.ld (show 8 * sArr a + 8 ≤ L.Z by
      have := hdr_lt_slot L.w 8 (show sArr a < 32 by unfold sArr; omega); have := hg.2; omega)]

theorem small256_ct {a : Nat} (ha : a < 8)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block [ldh .x8 (sArr a), movi .x7 0]) hc).isSome = true) :
    RelCT isa (Two GoodL) (Arithmetic.small a 256) (fun _ _ => True) := by
  unfold Arithmetic.small
  refine RelCT.seq (two_piece (Ψ := SmallHead) [.x0] pins_good (by taint_decide) ?_) ?_
  · intro L s hg
    refine WP.mono (WP.keep [.x12, .x9, .x13] (Q := fun t =>
      t.gpr .x12 = BitVec.ofNat 64 L.w ∧ t.gpr .x13 = 0 ∧ t.mem = s.mem) ?_ rfl rfl rfl)
      fun t ⟨⟨h12, hcx, hm⟩, hk⟩ =>
        ⟨⟨⟨hg.1.scr.congr hk.wr, (hk.gpr .x0 (by decide)).trans hg.1.x0, hm ▸ hg.1.hdr⟩, hg.2⟩, h12, hcx⟩
    brun [hg.1.x0, hdr_enc (show sW < 32 by decide), hg.1.hdr.hw,
      hg.1.scr.ld (show 8 * sW + 8 ≤ L.Z by have := hdr_lt_slot L.w 8 (show sW < 32 by decide); have := hg.2; omega)]
  rw [setWord_eq]
  refine RelCT.seq (two_piece (Ψ := fun L t => t.gpr .x8 = off L.B (slot L.w a) ∧
    t.gpr .x12 = BitVec.ofNat 64 L.w ∧ t.gpr .x13 = 0 ∧ t.gpr .x7 = 0) [.x0]
    (fun L s t hs ht => pins_good L s t hs.1 ht.1) hT ?_)
    (two_taint [.x8, .x12, .x13, .x7] (fun L s t hs ht r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.2.2.1.trans ht.2.2.1.symm
      · exact hs.2.2.2.trans ht.2.2.2.symm) (by taint_decide))
  intro L s ⟨hg, h12, hcx⟩
  refine WP.mono (WP.keep [.x8, .x7] (Q := fun t => t.gpr .x8 = off L.B (slot L.w a) ∧ t.gpr .x7 = 0) ?_ rfl rfl rfl)
    fun t ⟨⟨h8, h7⟩, hk⟩ => ⟨h8, (hk.gpr .x12 (by decide)).trans h12, (hk.gpr .x13 (by decide)).trans hcx, h7⟩
  brun [hg.1.x0, hdr_enc (show sArr a < 32 by unfold sArr; omega), hg.1.hdr.harr a ha,
    hg.1.scr.ld (show 8 * sArr a + 8 ≤ L.Z by
      have := hdr_lt_slot L.w 8 (show sArr a < 32 by unfold sArr; omega); have := hg.2; omega)]

/-- Bounds and the public modulus needed by constants setup. -/
def SetupPre (p : ProductPublic) (s : State) : Prop :=
  ModCtx s p.layout.B p.layout.Z p.layout.w p.layout.minv p.modulus ∧
    p.layout.w ≤ 48 ∧ 1 < p.modulus ∧ p.modulus % 2 = 1

theorem SetupPre.keep {p : ProductPublic} {s t : State} (h : SetupPre p s) (hm : t.mem = s.mem)
    {rs : List Reg} (k : Keep rs s t) (h0 : .x0 ∉ rs) : SetupPre p t :=
  ⟨⟨⟨h.1.good.scr.congr k.wr, (k.gpr .x0 h0).trans h.1.good.x0, hm ▸ h.1.good.hdr⟩,
    hm ▸ h.1.modulus, hm ▸ h.1.inverse⟩, h.2⟩

/-- Initializing one array retains the setup precondition. -/
theorem setup_one {a : Nat} (ha : a < 8) (han : a ≠ aN)
    {p : ProductPublic} {s : State} (h : SetupPre p s) :
    WP isa (Arithmetic.small a 1) s fun t =>
      SetupPre p t ∧ wv t.mem p.layout.B (slot p.layout.w a) p.layout.w = 1 := by
  refine WP.mono (one_ok h.1.good p.fits p.lower p.upper ha) fun t ⟨ht, hv, hf, _⟩ => ?_
  have hz : p.layout.B.toNat + slot p.layout.w 8 ≤ 2 ^ 64 := by
    have := h.1.good.scr.nowrap; have := p.fits; omega
  have hnot : aN ∉ [a] := by simpa using Ne.symm han
  refine ⟨⟨⟨ht, (hf.wv_of_not_mem (by decide) hnot hz).trans h.1.modulus, ?_⟩, h.2⟩, hv⟩
  rw [hf.word0_of_not_mem (by decide) hnot hz (by have := p.lower; omega)]
  exact h.1.inverse

/-- Setup's doubling loop has a public count even when the modulus is padded. -/
theorem doublingR2_ct : RelCT isa (Two SetupPre) Arithmetic.doublingR2 (fun _ _ => True) := by
  unfold Arithmetic.doublingR2 seqs
  refine RelCT.seq (two_post (Ψ := fun p s => SetupPre p s ∧
    wv s.mem p.layout.B (slot p.layout.w aR2) p.layout.w = 1)
    (two_map (fun p : ProductPublic => p.layout) (fun p _ h => ⟨h.1.good, p.fits⟩)
      (small_ct (a := aR2) (by decide) (by taint_decide)))
    (fun _ _ h => setup_one (by decide) (by decide) h)) ?_
  refine RelCT.seq (two_piece (Ψ := fun p s => SetupPre p s ∧
    wv s.mem p.layout.B (slot p.layout.w aR2) p.layout.w = 1 ∧
    s.gpr .x13 = BitVec.ofNat 64 (128 * p.layout.w)) [.x0]
    (fun p s t hs ht => pins_good p.layout s t ⟨hs.1.1.good, p.fits⟩ ⟨ht.1.1.good, p.fits⟩)
    (by taint_decide) ?_) ?_
  · intro p s ⟨h, hv⟩
    refine WP.mono (r2Count_ok h.1.good p.fits) fun t ⟨ht, hcx, hm, _⟩ => ?_
    exact ⟨⟨⟨ht, hm ▸ h.1.modulus, hm ▸ h.1.inverse⟩, h.2⟩, hm ▸ hv, hcx⟩
  exact (two_map (fun p : ProductPublic => (⟨p.layout, 128 * p.layout.w⟩ : DblPub))
    (fun p s ⟨h, hv, hcx⟩ => ⟨⟨h.1.good, p.fits⟩, p.lower, p.upper,
      by change 1 ≤ 128 * p.layout.w; have := p.lower; omega,
      by change 128 * p.layout.w < 2 ^ 31; have := h.2.1; omega, hcx,
      by rw [hv, h.1.modulus]; exact h.2.2.1⟩)
    (doubles_ct (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide))).mono
    (fun _ _ h => h) (fun _ _ _ => True.intro)

/-- The storage width and the modulus' base, loaded for the top-word test. -/
def SetupRegs (p : ProductPublic) (s : State) : Prop :=
  SetupPre p s ∧ s.gpr .x12 = BitVec.ofNat 64 p.layout.w ∧
    s.gpr .x8 = off p.layout.B (slot p.layout.w aN)

/-- The branch register holds the public modulus' top word. -/
def SetupTested (p : ProductPublic) (s : State) : Prop :=
  SetupPre p s ∧ (s.gpr .x3).toNat = p.modulus / 2 ^ (64 * (p.layout.w - 1))

theorem constants_ct (M : Mont) : RelCT isa (Two SetupPre)
    (Arithmetic.constants M.mm) (fun _ _ => True) := by
  unfold Arithmetic.constants
  refine RelCT.seq (two_post (Ψ := SetupPre)
    (two_map (fun p : ProductPublic => p.layout) (fun p _ h => ⟨h.1.good, p.fits⟩)
      (small_ct (a := aOne) (by decide) (by taint_decide)))
    (fun _ _ h => WP.mono (setup_one (by decide) (by decide) h) fun _ ht => ht.1)) ?_
  unfold Arithmetic.topWord
  refine RelCT.seq (RelCT.block_append (l₁ := ([ldh .x12 sW, ldh .x8 (sArr aN)] : List Instr))
    (l₂ := ([.subImm .x .x4 .x12 1, .lsl .x .x4 .x4 3, .add .x .x4 .x8 .x4, ld .x3 .x4] : List Instr))
    (RelCT.seq (two_piece (Ψ := SetupRegs) [.x0]
      (fun p s t hs ht => pins_good p.layout s t ⟨hs.1.good, p.fits⟩ ⟨ht.1.good, p.fits⟩)
      (by taint_decide) ?_)
      (two_piece (Ψ := SetupTested) [.x12, .x8] ?_ (by taint_decide) ?_))) ?_
  · intro p s h
    have hg := h.1.good
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.layout.B (8 * i)) 8 := fun i hi =>
      hg.scr.ld (by have := hdr_lt_slot p.layout.w 8 hi; have := p.fits; omega)
    refine WP.mono (WP.keep [.x8, .x12] (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 p.layout.w ∧
        t.gpr .x8 = off p.layout.B (slot p.layout.w aN) ∧ t.mem = s.mem) (by
      brun [hg.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show sArr aN < 32 by decide),
        hl sW (by decide), hl (sArr aN) (by decide), hg.hdr.hw, hg.hdr.harr aN (by decide)])
      (by decide) (by decide) (by decide +kernel))
      fun t ⟨⟨h12, h8, hm⟩, k⟩ => ⟨h.keep hm k (by decide), h12, h8⟩
  · intro p s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.2.1.trans ht.2.1.symm
    · exact hs.2.2.trans ht.2.2.symm
  · intro p s ⟨h, h12, h8⟩
    have hg := h.1.good
    have hw2 := p.lower
    have hn := hg.scr.nowrap
    have := slot_le (w := p.layout.w) (show aN < 8 by decide)
    have hw8 : (BitVec.ofNat 64 p.layout.w - BitVec.ofNat 64 1) <<< 3 =
        BitVec.ofNat 64 (8 * (p.layout.w - 1)) := by
      apply BitVec.eq_of_toNat_eq
      have := p.upper
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega
    have htop := setup_top (s := s) hw2 h.1.modulus
    refine WP.mono (WP.keep [.x3, .x4] (Q := fun t =>
        t.gpr .x3 = word s.mem p.layout.B (slot p.layout.w aN + 8 * (p.layout.w - 1)) ∧
        t.mem = s.mem) (by
      brun [h12, h8, hw8, off_add,
        hg.scr.ld (show slot p.layout.w aN + 8 * (p.layout.w - 1) + 8 ≤ p.layout.Z by
          have := p.fits; omega)])
      (by decide) (by decide) (by decide +kernel))
      fun t ⟨⟨h3, hm⟩, k⟩ => ⟨h.keep hm k (by decide), by rw [h3, htop]⟩
  refine two_ite (fun p s t hs ht => by rw [eval_zero, eval_zero, eq_zero_iff, eq_zero_iff, hs.2, ht.2])
    ?_ ?_
  · exact two_map id (fun _ _ ⟨⟨h, _⟩, _⟩ => h) doublingR2_ct
  · refine two_map (fun p : ProductPublic => (⟨p.layout, p.modulus⟩ : R2Pub)) ?_ (r2_ct M)
    rintro p s ⟨⟨h, h3⟩, hc⟩
    rw [eval_zero, eq_zero_iff, h3] at hc
    simp only [Option.some.injEq, decide_eq_false_iff_not] at hc
    refine ⟨⟨h.1.good, p.fits⟩, p.lower, ?_, h.1.modulus, h.1.inverse, h.2.2.2, ?_⟩
    · change p.layout.w < 2 ^ 30
      have := h.2.1; omega
    · change 2 ^ (64 * (p.layout.w - 1)) ≤ p.modulus
      by_contra hl
      exact hc (Nat.div_eq_of_lt (by omega))

end VG.Proof.Dsa.AArch64
