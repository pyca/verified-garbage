module

public import VerifiedGarbage.Proof.Ffdh.AArch64.CheckPublic.Stages
meta import VerifiedGarbage.Proof.Ffdh.AArch64.CheckPublic.Stages
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.PowLit
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
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckPublic.Correct
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
meta import VerifiedGarbage.Proof.Ffdh.AArch64.CheckPublic.Correct
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
# `vg_ffdh_check_public` on AArch64: constant time

Runs with the same public data (`CpP`: here every input) leak the same
(`cp_constantTime`): each piece of `CheckPublic.code` is constant time for
its stage (`Stages.lean`), by RSA's and the front's claims or the taint
analysis, and its branches test what the stage fixes.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.CheckPublic

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

theorem pins_nil {α : Type} (Φ : α → State → Prop) : Pins Φ [] := fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

theorem main_eq (W : Window) (M : Mont) (S : Selector) :
    CheckPublic.main W.code S.code M.mm = seqs ((([.block head] : List (Prog isa)) ++ pSetup) ++ (Crt.loadArr aXm sY sK ++
      (range aXm ++ ([.ite (.zero .x .x9) (VG.Impl.Ffdh.AArch64.Domain.ret 0)
        (.seq (.block ([leave] ++ qTest)) (.ite (.zero .x .x3) (VG.Impl.Ffdh.AArch64.Domain.ret 1)
          (seqs (CheckPublic.subgroup W.code S.code M.mm))))] : List (Prog isa))))) := by
  simp only [CheckPublic.main, List.append_assoc, List.singleton_append]

theorem subgroup_eq (W : Window) (M : Mont) (S : Selector) :
    CheckPublic.subgroup W.code S.code M.mm = scan sQ ++ (.block [enter] :: (r2Steps M.mm ++
      (pow W.code S.code M.mm sY sK sEp sEl ++ (isOne aY ++ ([.block [mov .x0 .x9]] : List (Prog isa)))))) := by
  simp only [CheckPublic.subgroup, List.append_assoc, List.cons_append, List.nil_append]

/-- With q: its scan, `R² mod p`, `y^q mod p` and its comparison with 1. -/
theorem subgroup_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two fun p s => C4 p s ∧ isa.eval (.zero .x .x3) s = some false)
      (seqs (CheckPublic.subgroup W.code S.code M.mm)) fun _ _ => True := by
  rw [subgroup_eq]
  refine RelCT.seqs_append (by simp [scan]) (by simp) (RelCT.seq (R := Two C5)
    (two_post (two_map CpP.qs (fun p s h => c4_scan p s h.1 h.2) (scan_ct (by taint_decide) (by taint_decide)))
      fun p s h => c4_c5 p s h.1 h.2) ?_)
  refine seqs_cons_ct (by simp [r2Steps]) (RelCT.seq (R := Two C6)
    (two_piece [.x0] (pins_x0B CpP.B fun _ _ h => c5_x0 h) (by taint_decide) c5_c6) ?_)
  refine RelCT.seqs_append (by simp [r2Steps]) (by simp [pow]) (RelCT.seq (R := Two C7)
    (two_post ((r2_ct M).mono (fun _ _ h => two_bind (fun p s₁ s₂ ⟨mi₁, hI₁, hm, _⟩ ⟨mi₂, hI₂, _⟩ => by
      have c := hI₁.1.ctx
      obtain ⟨hodd, -⟩ := valid_facts hm c.k1
      have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega
      have := c.k1
      obtain rfl := xvals_minv (show 1 ≤ p.w by omega) hodd hI₁.2.2.1 hI₂.2.2.1
      exact ⟨_, c6_r2 hI₁ hm, c6_r2 hI₂ hm⟩) h) fun _ _ h => h) (c6_c7 M)) ?_)
  refine RelCT.seqs_append (by simp [pow]) (by simp [isOne, eqArr]) (RelCT.seq (R := Two C8)
    (two_post (two_map CpP.pw c7_ps0 (pow_ct W M S (loadArr_ct (by decide) (by taint_decide) (by taint_decide))
      (expLoop_ct W M S (by taint_decide)) (by taint_decide) (by taint_decide) (by taint_decide)))
      (c7_c8 W M S)) ?_)
  refine RelCT.seqs_append (by simp [isOne, eqArr]) (by simp) (RelCT.seq
    (R := Two fun (_ : CpP) (_ : State) => True)
    (two_post (two_map CpP.ws (fun _ _ h => h.1) (eqArr_ct (by decide) (by decide) (by taint_decide)))
      fun p s ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ => WP.mono (eqArr_ok hg hZ hw hw' (show aY < 8 by decide)
        (show aOne < 8 by decide)) fun _ _ => trivial) ?_)
  · rw [seqs_one]
    exact two_taint [] (pins_nil _) (by taint_decide)

/-- `main`, for a valid p. -/
theorem main_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two fun p s => CE p s ∧ isa.eval (.zero .x .x9) s = some false)
      (CheckPublic.main W.code S.code M.mm) fun _ _ => True := by
  rw [main_eq]
  refine RelCT.seqs_append (by simp [pSetup]) (by simp [Crt.loadArr]) (RelCT.seq (R := Two C1)
    (two_post (two_map CpP.d (fun p s h => ce_setupP p s h.1 h.2) setup_ct) fun p s h => ce_c1 p s h.1 h.2) ?_)
  refine RelCT.seqs_append (by simp [Crt.loadArr]) (by simp) (RelCT.seq (R := Two C2)
    (two_post (two_map CpP.yl c1_lpre (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) c1_c2) ?_)
  refine RelCT.seqs_append (by simp [range, gt1, ltArr, cmpArr]) (by simp) (RelCT.seq (R := Two C3)
    (two_post (two_map CpP.ws c2_goodW1 (range_ct (by decide) (by decide) (by taint_decide) (by taint_decide)
      (by taint_decide))) c2_c3) ?_)
  rw [seqs_one]
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by rw [c3_eval h₁, c3_eval h₂])
    (two_taint [] (pins_nil _) (by taint_decide)) ?_
  refine RelCT.seq (R := Two C4) (RelCT.block_append (RelCT.seq (two_piece (Ψ := fun (p : CpP) t =>
      t.gpr .x0 = p.B ∧ WP isa (.block qTest) t (C4 p)) [.x0]
      (pins_x0B (fun p => off p.B (inner p.w)) fun _ _ ⟨⟨_, ⟨_, hc, _⟩, _⟩, _⟩ => hc.x0) (by taint_decide)
      fun p s h => wp_and (c3_leave p s h.1) (WP.block_append_iff.mp (c3_c4 p s h.1)))
    (two_piece [.x0] (pins_x0B CpP.B fun _ _ h => h.1) (by taint_decide) fun _ _ h => h.2))) ?_
  exact two_ite (fun p s₁ s₂ h₁ h₂ => by rw [c4_eval h₁, c4_eval h₂])
    (two_taint [] (pins_nil _) (by taint_decide)) (subgroup_ct W M S)

/-- `CheckPublic.code` leaks the same in runs with the same public data. -/
theorem cp_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two CR) (CheckPublic.code W.code S.code M.mm) fun _ _ => True := by
  unfold CheckPublic.code
  refine RelCT.seq (R := Two CE) (RelCT.block_append (RelCT.seq (two_piece (Ψ := E1) [.x0, .x1, .x2, .x3, .x5]
      (pins_of entryRegs cr_regs) (by taint_decide) cr_e1)
    (two_post (two_map CpP.d e1_dhp domHead_ct) e1_ce))) ?_
  exact two_ite (fun p s₁ s₂ h₁ h₂ => by rw [ce_eval h₁, ce_eval h₂])
    (two_taint [] (pins_nil _) (by taint_decide)) (main_ct W M S)

/-- The public data of a state. -/
def cpOf (s : State) : CpP :=
  ⟨s.gpr .x5, (s.gpr .x6).toNat * 8, (s.gpr .x2).toNat, (s.gpr .x1).toNat, s.gpr .x0, s.gpr .x3, cpDom s,
    Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat, s.sp⟩

/-- `vg_ffdh_check_public` is constant time. -/
theorem cp_constantTime (W : Window) (M : Mont) (S : Selector) :
    ConstantTime isa cpContract.pre cpContract.pub (CheckPublic.code W.code S.code M.mm) := by
  refine RelCT.constantTime ((cp_ct W M S).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨cpOf s₁, ?_, ?_, hp.1⟩) fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6⟩ := hp
    unfold cpLeak at hl
    obtain ⟨hd, hy⟩ := List.append_inj hl (by simp [cpDom, Spec.Rsa.bytesAt, r1])
    refine ⟨h₂, hsp.symm, r5.symm, by rw [← r6]; rfl, by rw [← r2]; rfl, by rw [← r1]; rfl, r0.symm, r3.symm, ?_, ?_⟩
    · exact ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hd).symm
    · exact ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hy).symm

end VG.Proof.Ffdh.AArch64.CheckPublic
