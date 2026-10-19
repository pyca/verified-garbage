module

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowDispatchCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowDispatchCT

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTCode
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowDispatch
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTCode

import Mathlib.Data.Int.ModEq
meta import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
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
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTN
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
import VerifiedGarbage.Proof.Bignum.AArch64.CrtEntry
import VerifiedGarbage.Proof.Bignum.AArch64.CrtMain
import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAdvance
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedGroup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedGroupCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedStep
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowConstantTime
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExpCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinish
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinishSquare
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFrameContext
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroupCore
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroupLoop
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroups
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowHead
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowLayout
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowLoopControl
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowMain
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowP
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPending
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPendingMath
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawCore
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawSquares
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRun
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowSetup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowSquares
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowStep
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailBit
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailByteCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
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
import VerifiedGarbage.Proof.Bignum.CrtWindowPRanges
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
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
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTN
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtEntry
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAdvance
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedGroup
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedGroupCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedStep
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowConstantTime
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExpCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinishSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFrameContext
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroupCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroupLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroups
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowHead
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowLoopControl
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowP
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPending
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPendingMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawSquares
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRun
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowSquares
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowStep
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailBit
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailByteCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Double
meta import VerifiedGarbage.Proof.Bignum.AArch64.Mont
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
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
meta import VerifiedGarbage.Proof.Bignum.CrtWindowPRanges
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-!
# `vg_rsa_private_crt` on AArch64: constant time

`entry` and the modulus' check leak the same in runs that agree on the
public data (the arguments but the input and the key's values, and `n`),
and so do `fail` and `main` (`crtMain_ct`): `crtCode_ct`, and the contract's
`ConstantTime` (`crtCode_constantTime_of`), given that `n`'s setup is
constant time.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Rsa.AArch64 (crtA stackArgs_ten)

/-- `vg_rsa_private_crt` leaks the same in runs that agree on the public data,
given that `main`'s parts do. -/
theorem crtCode_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two CCRel) (VG.Impl.Rsa.AArch64.WindowFive.code W.code S.code M.mm) (fun _ _ => True) := by
  unfold VG.Impl.Rsa.AArch64.WindowFive.code
  refine RelCT.seq (R := Two CC3) ?_ ?_
  · rw [head_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := CC1) [.x2, .x3] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.2.2.2.2.2.2.1, h₂.2.2.2.2.2.2.1]
      · rw [h₁.x3, h₂.x3]) (by taint_decide) ?_)
      (two_piece [.x8, .x2, .x3] (fun p s₁ s₂ ⟨_, _, a₁, b₁, c₁, _⟩ ⟨_, _, a₂, b₂, c₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]
        · rw [c₁, c₂]) (by taint_decide) fun p t ⟨s, hs, _, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := crtCtx_of hs.1
    have hh : WP isa (.block (([.ldrSp .x8 64] : List Instr) ++ (entry.drop 1 ++ invalid))) s (HeadPost s) := by
      rw [← head_split]; exact crtHeadChk_ok c
    have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 64) 64 = stackArg s 8 := rfl
    have ha8 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 64) 8 := c.ha 8 (by decide)
    have ho : 64 % 8 = 0 ∧ 64 < 32768 := ⟨rfl, by decide⟩
    refine WP.mono (wp_and (WP.block_append_iff.mp hh) (WP.keep [.x8] (Q := fun t => t.gpr .x8 = stackArg s 8)
      (by brun [exec_ldrSp ho ha8, hB']) (by decide) (by decide) (by decide +kernel))) fun t ⟨hw, h8, k⟩ =>
        ⟨s, hs, h8.trans hs.2.2.1, (k.gpr .x2 (by decide)).trans hs.2.2.2.2.2.2.1,
          (k.gpr .x3 (by decide)).trans hs.x3, hw⟩
  -- `fail` or `main`.
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, cc3_x9 h₁, cc3_x9 h₂]) ?_ ?_
  · -- `fail`.
    unfold Precomputed.fail
    have pin : ∀ p t, (CC3 p t ∧ isa.eval (.zero .x .x9) t = some true) → t.gpr .x0 = p.m.B := fun p t ⟨h, _⟩ => by
      obtain ⟨_, _, _, _, _, _, hpre⟩ := cc3_pre h
      exact hpre.x0
    refine RelCT.seq (two_piece (Ψ := fun (p : CCPub) t => t.gpr .x1 = p.m.op + BitVec.ofNat 64 0 ∧
        t.gpr .x2 = BitVec.ofNat 64 p.m.k ∧ t.gpr .x0 = p.m.B) [.x0]
      (pins_x0B (fun p : CCPub => p.m.B) pin) (by taint_decide) ?_)
      (two_taint [.x1, .x2, .x0] (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) (by taint_decide))
    rintro p t ⟨h, -⟩
    obtain ⟨_, _, _, _, _, _, hpre⟩ := cc3_pre h
    have hn := hpre.scr.nowrap
    have hk1 := hpre.k1
    have hk2 := hpre.k2
    have hZq := hpre.z
    have h8 := hdr_lt_slot ((p.m.k + 7) / 8) 8 (show 31 < 32 by decide)
    have hZ : 8 * 32 ≤ p.m.Z := by unfold offQ at hZq; omega
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off p.m.B (8 * i)) 8 := fun i hi => hpre.scr.ld (by omega)
    refine WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t' => t'.gpr .x1 = p.m.op + BitVec.ofNat 64 0 ∧
        t'.gpr .x2 = BitVec.ofNat 64 p.m.k) (by
      brun [hpre.x0, hdr_enc (show Public.sOut < 32 by decide), hdr_enc (show Public.sK < 32 by decide),
        hl Public.sOut (by decide), hl Public.sK (by decide), hpre.hO, hpre.hK]) (by decide) (by decide)
      (by decide +kernel))
      fun t' ⟨⟨h1, h2⟩, k'⟩ => ⟨h1, h2, (k'.gpr .x0 (by decide)).trans hpre.x0⟩
  · -- `main`.
    have toM : ∀ p t, CC3 p t ∧ isa.eval (.zero .x .x9) t = some false → OldStage p.m t := by
      rintro p t ⟨h, he⟩
      obtain ⟨xb, pb, qb, dpb, dqb, qib, hpre⟩ := cc3_pre h
      have hv : Spec.Rsa.modulusValid p.m.N p.m.k = true := by
        rw [eval_zero, cc3_x9 h] at he
        revert he
        cases Spec.Rsa.modulusValid p.m.N p.m.k <;> decide
      exact ⟨t, xb, pb, qb, dpb, dqb, qib, hpre, hv, rfl⟩
    exact (dispatch_ct W M S).mono (fun _ _ h => two_bind (fun p t₁ t₂ h₁ h₂ =>
      ⟨p.m, toM p t₁ h₁, toM p t₂ h₂⟩) h) fun _ _ h => h

/-- `vg_rsa_private_crt` is constant time, given that `main`'s parts are. -/
theorem crtCode_constantTime_of (W : Window) (M : Mont) (S : Selector) :
    ConstantTime isa crtA.pre crtA.pub (VG.Impl.Rsa.AArch64.WindowFive.code W.code S.code M.mm) := by
  refine RelCT.constantTime ((crtCode_ct W M S).mono
    (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨ccPubOf s₁, ?_, ?_, hp.2.1⟩) fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hr, hsp, ha, hn⟩ := hp
    simp only [stackArgs_ten, List.cons.injEq, and_true] at ha
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := ha
    have r : ∀ r ∈ argRegs, s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    exact ⟨h₂, hsp.symm, a8.symm, by rw [← a9]; rfl, by rw [r .x3 (by decide)]; rfl, r .x0 (by decide), r .x2 (by decide),
      r .x4 (by decide), r .x6 (by decide), a0.symm, a2.symm, a4.symm, a6.symm, by rw [r .x7 (by decide)]; rfl,
      by rw [← a1]; rfl, hn.symm⟩


end VG.Proof.Bignum.AArch64.WindowFive
