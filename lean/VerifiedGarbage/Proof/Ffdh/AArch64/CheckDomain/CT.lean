module

public import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.Correct
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
meta import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.Correct
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.Pieces
meta import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.Pieces
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExpCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExpCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Block
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
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAdvance
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedGroup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedGroupCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedStep
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinish
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinishSquare
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFrameContext
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroupCore
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroupLoop
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroups
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowHead
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowLoopControl
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPending
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPendingMath
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawCore
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawSquares
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRun
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowSquares
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowStep
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailBit
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailByteCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
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
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Spec.Dsa.SignVerify
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
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAdvance
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedGroup
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedGroupCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedStep
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinishSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFrameContext
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroupCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroupLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroups
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowHead
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowLoopControl
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPending
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPendingMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawSquares
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRun
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowSquares
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowStep
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailBit
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailByteCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Double
meta import VerifiedGarbage.Proof.Bignum.AArch64.Mont
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
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
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Spec.Dsa.SignVerify

/-!
# `vg_ffdh_check_domain` on AArch64: constant time

Runs with the same public data (`CdP`: every input) leak the same
(`cd_constantTime`): each piece of `CheckDomain.code` is constant time for
its stage (`Stages.lean`), by RSA's and the front's claims or the taint
analysis, and its branches test what the stage fixes.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.CheckDomain

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave zeroArr)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

theorem pins_nil {α : Type} (Φ : α → State → Prop) : Pins Φ [] := fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

/-- q's range checks. -/
theorem qblk_ct : RelCT isa (Two GoodW1) (seqs qblk) fun _ _ => True := by
  unfold qblk gt1
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine RelCT.seqs_append (by simp [isOdd]) (by simp) (RelCT.seq (R := Two GoodW1)
    (two_post ((isOdd_ct (show aXm < 8 by decide) (by taint_decide)).mono (fun _ _ h => two_goodW1 h)
      fun _ _ h => h) fun L s h => ?_) ?_)
  · obtain ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ := h
    exact WP.mono (isOdd_ok hg hZ hw (show aXm < 8 by decide)) fun t ⟨_, hm, k⟩ =>
      GoodW1.keep ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ hm (k.gpr .x0 (by decide)) k.wr
  refine seqs_cons_ct (by simp [ltArr, cmpArr]) (RelCT.seq (R := Two GoodW1)
    (two_piece [.x0] pins_goodW1 (by taint_decide) (stF_ok (by decide) (by decide))) ?_)
  refine RelCT.seqs_append (by simp [ltArr, cmpArr]) (by simp) (RelCT.seq (R := Two GoodW1)
    (two_post ((ltArr_ct (show aOne < 8 by decide) (show aXm < 8 by decide) (by taint_decide)).mono
      (fun _ _ h => two_goodW1 h) fun _ _ h => h) fun L s h => ?_) ?_)
  · obtain ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ := h
    exact WP.mono (ltArr_ok hg hZ hw hw' (show aOne < 8 by decide) (show aXm < 8 by decide)) fun t ⟨_, hm, k⟩ =>
      GoodW1.keep ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ hm (k.gpr .x0 (by decide)) k.wr
  refine seqs_cons_ct (by simp [ltP, Crt.copyArr]) (RelCT.seq (R := Two GoodW1)
    (two_piece [.x0] pins_goodW1 (by taint_decide) andF_ok) ?_)
  refine RelCT.seqs_append (by simp [ltP, Crt.copyArr]) (by simp) (RelCT.seq (R := Two GoodW1)
    (two_post (ltP_ct (show aXm < 8 by decide) (by decide) (by taint_decide) (by taint_decide)) fun L s h => ?_) ?_)
  · obtain ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ := h
    have hT0 := hdr_lt_slot L.w aTmp (show 31 < 32 by decide)
    exact WP.mono (ltP_ok hg hZ hw hw' (show aXm < 8 by decide) (by decide)) fun t ⟨_, ho, k⟩ =>
      GoodW1.of_outside ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ (by omega) ho k.wr (k.gpr .x0 (by decide))
  rw [seqs_one]
  exact two_taint [.x0] pins_goodW1 (by taint_decide)

/-- The outer workspace, as `zeroArr` sees it. -/
abbrev _root_.VG.Proof.Ffdh.AArch64.FD.ows (D : FD) : Ws := ⟨D.B, D.Z, D.w⟩

theorem _root_.VG.Proof.Ffdh.AArch64.Pa.goodW {D : FD} {mi : BitVec 64} {t : State} (h : Pa D mi t) : GoodW D.ows t :=
  let ⟨hg, hZ⟩ := h.outer.good
  ⟨_, hg, hZ⟩

/-- `p − 1` into the outer array `aX`. -/
theorem pMinus1_ct : RelCT isa (Two fun (D : FD) t => ∃ mi, Pa D mi t) (seqs CheckDomain.pMinus1)
    fun _ _ => True := by
  unfold CheckDomain.pMinus1
  simp only [seqs]
  refine RelCT.seq (R := Two fun (D : FD) t => ∃ mi, Pa D mi t)
    (two_post (two_map FD.ows (fun _ _ ⟨_, h⟩ => h.goodW) (zeroArr_ct (show aX < 8 by decide) (by taint_decide)))
      fun D s ⟨mi, h⟩ => WP.mono h.zeroX fun _ h' => ⟨mi, h'⟩) ?_
  refine RelCT.seq (two_piece (Ψ := fun (D : FD) u => (u.gpr .x1 = D.dp ∧
      u.gpr .x2 = BitVec.ofNat 64 D.k ∧ u.gpr .x8 = off D.B (slot D.w aX)) ∧
      WP isa loadBE u fun v => v.gpr .x0 = D.B ∧ v.gpr .x8 = off D.B (slot D.w aX)) [.x0]
    (pins_x0B FD.B fun _ _ ⟨_, h⟩ => h.2.2.2.2.2.2) (by taint_decide) fun D s ⟨mi, h⟩ => h.ldX) ?_
  refine RelCT.seq (two_piece (Ψ := fun (D : FD) v => v.gpr .x0 = D.B ∧ v.gpr .x8 = off D.B (slot D.w aX))
    [.x1, .x2, .x8]
    (pins_of (fun (D : FD) r => if r = .x1 then D.dp else if r = .x2 then BitVec.ofNat 64 D.k else
        off D.B (slot D.w aX)) fun D s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.1.1
      · exact h.1.2.1
      · exact h.1.2.2) (by taint_decide) fun _ _ h => h.2) ?_
  exact two_taint [.x8] (pins_of (fun (D : FD) _ => off D.B (slot D.w aX)) fun D s h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.2) (by taint_decide)

/-- A piece constant time, and its stage after it by correctness. -/
theorem ct_post {α : Type} {Φ Ψ : α → State → Prop} {c : Prog isa} (hct : RelCT isa (Two Φ) c fun _ _ => True)
    (hw : ∀ a s, Φ a s → WP isa c s fun u => Ψ a u ∧ KX s u) : RelCT isa (Two Φ) c (Two Ψ) :=
  two_post hct fun a s h => WP.mono (hw a s h) fun _ h => h.1

/-! ## The stages' hypotheses for the shared pieces -/

/-- p's workspace's public data. -/
abbrev CdP.mp (p : CdP) : MPub := ⟨p.D.B, p.D.Z, p.D.w, p.D.k, p.D.dp⟩

theorem q9_m1 (p : CdP) (t : State) (h : Q9 p t) : M1 sDom sK p.mp t := by
  obtain ⟨⟨hb, hO, hs, hm⟩, -⟩ := h
  have ew := hb.ew
  have := hb.k1
  exact ⟨p.D.dom.take p.D.k, hO, hs.get (by simp), hs.get (by simp), hb.dom.take p.D.k, hb.plen,
    show 1 ≤ p.D.k by omega, show p.D.k ≤ 8 * p.D.w by omega, (valid_facts hm hb.k1).1⟩

/-- q's workspace's public data. -/
abbrev CdP.mq (p : CdP) : MPub :=
  ⟨p.D.B, p.D.Z, p.D.w, p.D.k - lead p.D.qb, off (p.D.dp + BitVec.ofNat 64 (2 * p.D.k)) (lead p.D.qb)⟩

theorem q5_m1 (p : CdP) (t : State) (h : Q5 p t) : M1 sEp sEl p.mq t := by
  obtain ⟨mi, ⟨hP, hEp, hEl⟩, hq, hr, -⟩ := h
  have hb := hP.1
  obtain ⟨hl, h1, hk, hQ, hsrc⟩ := qe_facts hb hq
  have ew := hb.ew
  exact ⟨p.qe, hP.outer, hEl, hEp, hsrc, hl, show 1 ≤ p.D.k - lead p.D.qb by omega,
    show p.D.k - lead p.D.qb ≤ 8 * p.D.w by omega, by rw [hQ]; exact hr.1⟩

/-- The reduction's public data. -/
abbrev CdP.xq (p : CdP) : XPub := ⟨p.D.B, p.D.Z, inner p.D.w, p.D.w, p.wq⟩

theorem q6_rpre (p : CdP) (t : State) (h : Q6 p t) : RPre aX p.xq t := by
  obtain ⟨mq, hb, hc, hv, -, -, -, hq, hr, -⟩ := h
  have hw2 := hb.w2
  have hw28 := hb.w28
  have ew := hb.ew
  have := hb.qlen hq
  exact ⟨mq, p.Q, hc, hv, show 2 ≤ p.wq by unfold CdP.wq wsWords; omega,
    show p.wq ≤ p.D.w by unfold CdP.wq wsWords; omega, show p.D.w < 2 ^ 30 by omega, hr.2.1, by decide⟩

/-- q's workspace, as the comparison sees it. -/
abbrev CdP.wsq (p : CdP) : Ws := ⟨off p.D.B (inner p.D.w), slot p.wq 8, p.wq⟩

theorem q7_goodW (p : CdP) (t : State) (h : Q7 p t) : GoodW p.wsq t :=
  let ⟨mq, _, hc, _⟩ := h
  ⟨mq, hc.good, Nat.le_refl _⟩

theorem q12_goodW (p : CdP) (t : State) (h : Q12 p t) : GoodW p.D.ws t :=
  let ⟨mi, hM, _⟩ := h
  ⟨mi, hM.2.1.sub.good, Nat.le_refl _⟩

/-! ## The pieces -/

/-- After `q ∣ p − 1`. -/
theorem fin_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two fun p s => Q8 p s ∧ isa.eval (.zero .x .x9) s = some false) (seqs (fin W M S))
      fun _ _ => True := by
  rw [fin_eq]
  refine seqs_cons_ct (by simp [pSetup]) (RelCT.seq (R := Two Q9) (two_piece [.x0]
    (pins_x0B (fun p => off p.D.B (inner p.D.w)) fun _ _ ⟨⟨_, _, hc, _⟩, _⟩ => hc.x0) (by taint_decide)
    fun p s h => WP.mono (q8_q9 p s h.1 h.2) fun _ h => h.1) ?_)
  refine RelCT.seqs_append (by simp [pSetup]) (by simp [r2Steps]) (RelCT.seq (R := Two Q10)
    (show RelCT isa (Two Q9) (seqs pSetup) (Two Q10) from
      ct_post (two_map CdP.mp q9_m1 (wsMod_ct (by decide) (by decide) (by decide) (by decide) (by taint_decide)
        (by taint_decide) (by taint_decide))) q9_q10) ?_)
  refine RelCT.seqs_append (by simp [r2Steps]) (by simp [pow]) (RelCT.seq (R := Two Q11)
    (ct_post ((r2_ct M).mono (fun _ _ h => two_bind (fun p s₁ s₂ ⟨mi₁, hI₁, _⟩ ⟨mi₂, hI₂, _⟩ => by
      obtain rfl := hI₁.minv hI₂
      exact ⟨_, hI₁.r2pre, hI₂.r2pre⟩) h) fun _ _ h => h) (q10_q11 M)) ?_)
  refine RelCT.seqs_append (by simp [pow]) (by simp [isOne, eqArr]) (RelCT.seq (R := Two Q12)
    (ct_post (two_map _ q11_pre (pow_ct W M S (loadArr_ct (by decide) (by taint_decide) (by taint_decide))
      (expLoop_ct W M S (by taint_decide)) (by taint_decide) (by taint_decide) (by taint_decide)))
      (q11_q12 W M S)) ?_)
  refine RelCT.seqs_append (by simp [isOne, eqArr]) (by simp) (RelCT.seq (R := Two Q13)
    (show RelCT isa (Two Q12) (seqs (isOne aY)) (Two Q13) from
      ct_post (two_map (fun p : CdP => p.D.ws) q12_goodW (eqArr_ct (by decide) (by decide) (by taint_decide)))
        q12_q13) ?_)
  rw [seqs_one]
  exact two_taint [] (pins_nil _) (by taint_decide)

/-- After q's range. -/
theorem rest_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two fun p s => Q2 p s ∧ isa.eval (.zero .x .x9) s = some false) (seqs (rest W M S))
      fun _ _ => True := by
  rw [rest_eq]
  refine seqs_cons_ct (by simp [scan]) (RelCT.seq (R := Two Q3) (two_piece [.x0]
    (pins_x0B (fun p => off p.D.B (inner p.D.w)) fun _ _ ⟨⟨_, hI, _⟩, _⟩ => hI.2.1.x0) (by taint_decide)
    fun p s h => WP.mono (q2_q3 p s h.1 h.2) fun _ h => h.1) ?_)
  refine RelCT.seqs_append (by simp [scan]) (by simp [CheckDomain.pMinus1]) (RelCT.seq (R := Two Q4)
    (ct_post (two_map (fun p : CdP => p.D.qs) (fun p s ⟨_, hP, hq, _⟩ => hP.scanPre hq)
      (scan_ct (by taint_decide) (by taint_decide))) q3_q4) ?_)
  refine RelCT.seqs_append (by simp [CheckDomain.pMinus1]) (by simp) (RelCT.seq (R := Two Q5)
    (ct_post (two_map CdP.D (fun p s ⟨mi, ⟨hP, _⟩, _⟩ => ⟨mi, hP⟩) pMinus1_ct) q4_q5) ?_)
  refine RelCT.seqs_append (by simp) (by simp [Crt.redc]) (RelCT.seq (R := Two Q6)
    (ct_post (two_map CdP.mq q5_m1 (wsMod_ct (by decide) (by decide) (by decide) (by decide) (by taint_decide)
      (by taint_decide) (by taint_decide))) q5_q6) ?_)
  refine RelCT.seqs_append (by simp [Crt.redc]) (by simp) (RelCT.seq (R := Two Q7)
    (ct_post (two_map CdP.xq q6_rpre (redc_ct_of M (by taint_decide))) (q6_q7 M)) ?_)
  refine RelCT.seqs_append (by simp [isZero, ltArr, cmpArr]) (by simp) (RelCT.seq (R := Two Q8)
    (show RelCT isa (Two Q7) (seqs (isZero Crt.aXc)) (Two Q8) from
      ct_post (two_map CdP.wsq q7_goodW (ltArr_ct (by decide) (by decide) (by taint_decide))) q7_q8) ?_)
  rw [seqs_one]
  exact two_ite (fun p s₁ s₂ h₁ h₂ => by rw [q8_eval h₁, q8_eval h₂])
    (two_taint [] (pins_nil _) (by taint_decide)) (fin_ct W M S)

/-- With q. -/
theorem withQ_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two fun p s => S4 p s ∧ isa.eval (.zero .x .x3) s = some false)
      (seqs (CheckDomain.withQ W.code S.code M.mm)) fun _ _ => True := by
  rw [withQ_eq]
  refine seqs_cons_ct (by simp [Crt.loadArr]) (RelCT.seq (R := Two Q0) (two_piece [.x0]
    (pins_x0B (fun p => p.D.B) fun _ _ ⟨⟨_, hP, _⟩, _⟩ => hP.2.2.2.2.2.2) (by taint_decide)
    fun p s h => WP.mono (s4_q0 p s h.1 h.2) fun _ h => h.1) ?_)
  refine RelCT.seqs_append (by simp [Crt.loadArr]) (by simp) (RelCT.seq (R := Two Q1)
    (ct_post (two_map _ q0_lpre (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) q0_q1) ?_)
  refine RelCT.seqs_append (by simp [isOdd]) (by simp) (RelCT.seq (R := Two Q2)
    (ct_post (two_map (fun p : CdP => p.D.ws) (fun p s ⟨_, hI, _⟩ => hI.goodW1) qblk_ct) q1_q2) ?_)
  rw [seqs_one]
  exact two_ite (fun p s₁ s₂ h₁ h₂ => by rw [q2_eval h₁, q2_eval h₂])
    (two_taint [] (pins_nil _) (by taint_decide)) (rest_ct W M S)

/-- `main`, for a valid p. -/
theorem main_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two fun p s => CE (CdP.D p) s ∧ isa.eval (.zero .x .x9) s = some false)
      (CheckDomain.main W.code S.code M.mm) fun _ _ => True := by
  rw [main_eq]
  refine RelCT.seqs_append (by simp [pSetup]) (by simp [Crt.loadArr]) (RelCT.seq (R := Two S1)
    (ct_post (two_map (fun p : CdP => p.D.d) (fun p s h => ce_setupP _ s h.1 h.2) setup_ct)
      fun p s h => ce_in _ s h.1 h.2) ?_)
  refine RelCT.seqs_append (by simp [Crt.loadArr]) (by simp) (RelCT.seq (R := Two S2)
    (ct_post (two_map _ s1_lpre (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) s1_s2) ?_)
  refine RelCT.seqs_append (by simp [range, gt1, ltArr, cmpArr]) (by simp) (RelCT.seq (R := Two S3)
    (ct_post (two_map (fun p : CdP => p.D.ws) (fun p s ⟨_, hI, _⟩ => hI.goodW1) (range_ct (by decide) (by decide)
      (by taint_decide) (by taint_decide) (by taint_decide))) s2_s3) ?_)
  rw [seqs_one]
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by rw [s3_eval h₁, s3_eval h₂])
    (two_taint [] (pins_nil _) (by taint_decide)) ?_
  refine RelCT.seq (R := Two S4) (RelCT.block_append (l₁ := [leave]) (l₂ := qTest) (RelCT.seq
    (two_piece (Ψ := fun (p : CdP) t => t.gpr .x0 = p.D.B ∧ WP isa (.block qTest) t (S4 p)) [.x0]
      (pins_x0B (fun p => off p.D.B (inner p.D.w)) fun _ _ ⟨⟨_, hI, _⟩, _⟩ => hI.2.1.x0) (by taint_decide)
      fun p s h => ?_)
    (two_piece [.x0] (pins_x0B (fun p => p.D.B) fun _ _ h => h.1) (by taint_decide) fun _ _ h => h.2))) ?_
  · obtain ⟨mi, hI, _⟩ := h.1
    exact wp_and (WP.mono hI.leave fun _ h => h.1.2.2.2.2.2.2)
      (WP.block_append_iff.mp (WP.mono (s3_s4 p s h.1) fun _ h => h.1))
  exact two_ite (fun p s₁ s₂ h₁ h₂ => by rw [s4_eval h₁, s4_eval h₂])
    (two_taint [] (pins_nil _) (by taint_decide)) (withQ_ct W M S)

/-- `CheckDomain.code` leaks the same in runs with the same public data. -/
theorem cd_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two CR) (CheckDomain.code W.code S.code M.mm) fun _ _ => True := by
  unfold CheckDomain.code
  refine RelCT.seq (R := Two fun p => CE (CdP.D p)) (RelCT.block_append (RelCT.seq
    (two_piece (Ψ := fun p => E1 (CdP.D p)) [.x0, .x1, .x2, .x3] (pins_of entryRegs cr_regs) (by taint_decide)
      fun p s h => WP.mono (cr_e1 p s h) fun _ h => h.1)
    (ct_post (two_map (fun p : CdP => p.D.d) (fun _ _ h => h.dhp) domHead_ct) fun p s h => e1_ce _ s h))) ?_
  exact two_ite (fun p s₁ s₂ h₁ h₂ => by rw [ce_eval h₁, ce_eval h₂])
    (two_taint [] (pins_nil _) (by taint_decide)) (main_ct W M S)

/-- `vg_ffdh_check_domain` is constant time. -/
theorem cd_constantTime (W : Window) (M : Mont) (S : Selector) :
    ConstantTime isa cdContract.pre cdContract.pub (CheckDomain.code W.code S.code M.mm) := by
  refine RelCT.constantTime ((cd_ct W M S).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨cdOf s₁, cr_of s₁ h₁, ?_, hp.1⟩)
    fun _ _ h => h)
  obtain ⟨hsp, hd, r0, r1, r2, r3, r4⟩ := hp
  refine ⟨h₂, hsp.symm, r3.symm, by rw [← r4]; rfl, by rw [← r2]; rfl, by rw [← r1]; rfl, r0.symm, ?_⟩
  exact ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hd).symm

end VG.Proof.Ffdh.AArch64.CheckDomain
