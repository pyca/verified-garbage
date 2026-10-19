module
public import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Framework.Contract

import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinish
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinish
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignZero
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignZero
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
import VerifiedGarbage.Proof.Dsa.AArch64.CopyMasked
import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
import VerifiedGarbage.Proof.Dsa.AArch64.Failure
import VerifiedGarbage.Proof.Dsa.AArch64.Load
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopy
import VerifiedGarbage.Proof.Dsa.AArch64.RandomFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Setup
import VerifiedGarbage.Proof.Dsa.AArch64.Store
import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Digest
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
meta import VerifiedGarbage.Proof.Dsa.AArch64.CopyMasked
meta import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
meta import VerifiedGarbage.Proof.Dsa.AArch64.Failure
meta import VerifiedGarbage.Proof.Dsa.AArch64.Load
meta import VerifiedGarbage.Proof.Dsa.AArch64.Operands
meta import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopy
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.Setup
meta import VerifiedGarbage.Proof.Dsa.AArch64.Store
meta import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! Output clearing and publication reveal only the public status and addresses. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

structure RandomFinishPublic where
  B : Addr
  out : Addr
  len : Nat
  usedPtr : Addr
  status : BitVec 64

structure RandomFinishPre (p : RandomFinishPublic) (s : State) : Prop where
  scr : Scr s p.B Random.frameBytes
  sp : s.sp = p.B
  out : word s.mem p.B Random.oOut = p.out
  len : word s.mem p.B Random.oOutLen = BitVec.ofNat 64 p.len
  usedPtr : word s.mem p.B Random.oUsedPtr = p.usedPtr
  status : word s.mem p.B Random.oStatus = p.status
  positive : 0 < p.len
  bound : p.len < 2 ^ 64
  writes : ∀ j < p.len, InRegions s.wr (p.out + BitVec.ofNat 64 j) 1
  disjoint : ∀ d, d + 8 ≤ Random.frameBytes → Mem.Sep (off p.B d) 8 p.out p.len

def RandomFinishTailPre (p : RandomFinishPublic) (s : State) : Prop :=
  Scr s p.B Random.frameBytes ∧ s.sp = p.B ∧ word s.mem p.B Random.oUsedPtr = p.usedPtr

private theorem zero_ct : RelCT isa (Two RandomFinishPre) RandomSign.zeroOut (fun _ _ => True) := by
  unfold RandomSign.zeroOut
  refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .x12 = p.out ∧ s.gpr .x9 = BitVec.ofNat 64 p.len)
    [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide) ?_) ?_
  · intro p s h
    brun [exec_ldrSp (show Random.oOut % 8 = 0 ∧ Random.oOut < 32768 by decide),
      exec_ldrSp (show Random.oOutLen % 8 = 0 ∧ Random.oOutLen < 32768 by decide), h.sp, h.scr.ld (d := Random.oOut) (by decide),
      h.scr.ld (d := Random.oOutLen) (by decide), h.out, h.len]
  · apply two_taint [.x12, .x9] ?_ (by taint_decide)
    intro p s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.1.trans ht.1.symm
    · exact hs.2.trans ht.2.symm

private theorem zero_tail {p : RandomFinishPublic} {s : State} (h : RandomFinishPre p s) :
    WP isa RandomSign.zeroOut s (RandomFinishTailPre p) := by
  refine WP.mono (random_zeroOut_ok h.scr h.sp h.out h.len h.positive h.bound h.writes)
    fun t ⟨_, hf, hk⟩ => ?_
  exact ⟨h.scr.congr hk.wr, hk.sp.trans h.sp,
    (random_zero_preserves_word hf (h.disjoint _ (by decide)) h.bound).trans h.usedPtr⟩

private theorem header_ok {p : RandomFinishPublic} {s : State} (h : RandomFinishPre p s) :
    WP isa (.block (Random.statusTest 1)) s fun t =>
      RandomFinishPre p t ∧ (t.gpr .x4 == 0#64) = (p.status == 1) := by
  refine WP.mono (WP.keep [.x0, .x4] (Q := fun t =>
      t.mem = s.mem ∧ (t.gpr .x4 == 0#64) = (p.status == 1)) (by
        unfold Random.statusTest
        brun [exec_ldrSp (show Random.oStatus % 8 = 0 ∧ Random.oStatus < 32768 by decide),
          h.sp, h.scr.ld (d := Random.oStatus) (by decide), h.status]
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq, BitVec.sub_eq_iff_eq_add, BitVec.zero_add]
        rfl) rfl rfl rfl) fun t ⟨⟨hm, hz⟩, hk⟩ => ?_
  exact ⟨⟨h.scr.congr hk.wr, hk.sp.trans h.sp,
    by rw [hm]; exact h.out, by rw [hm]; exact h.len, by rw [hm]; exact h.usedPtr,
    by rw [hm]; exact h.status, h.positive, h.bound, by rw [hk.wr]; exact h.writes, h.disjoint⟩, hz⟩

private theorem clear_tail {p : RandomFinishPublic} {s : State} (h : RandomFinishTailPre p s) :
    WP isa (.block Random.clearNonce) s (RandomFinishTailPre p) := by
  refine WP.mono (random_clear_ok h.1 h.2.1) fun t ⟨hm, hk⟩ => ?_
  refine ⟨h.1.congr hk.wr, hk.sp.trans h.2.1, ?_⟩
  rw [hm, (random_clear_outside _ _).word (by decide) (by decide)]
  exact h.2.2

private theorem tail_ct : RelCT isa (Two RandomFinishTailPre)
    (.block (Random.clearNonce ++ ([.ldrSp .x2 Random.oUsedPtr,
      .ldrSp .x0 Random.oUsed, .str .x .x0 .x2 0,
      .ldrSp .x0 Random.oStatus] : List Instr))) (fun _ _ => True) := by
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := RandomFinishTailPre) []
    (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)
    (fun _ _ h => clear_tail h)) ?_
  change RelCT isa (Two RandomFinishTailPre) (.block
    (([.ldrSp .x2 Random.oUsedPtr, .ldrSp .x0 Random.oUsed] : List Instr) ++
    [.str .x .x0 .x2 0, .ldrSp .x0 Random.oStatus])) _
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun p s => s.sp = p.B ∧ s.gpr .x2 = p.usedPtr)
    [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide) ?_) ?_
  · intro p s ⟨hs, hsp, hu⟩
    brun [exec_ldrSp (show Random.oUsedPtr % 8 = 0 ∧ Random.oUsedPtr < 32768 by decide),
      exec_ldrSp (show Random.oUsed % 8 = 0 ∧ Random.oUsed < 32768 by decide),
      hsp, hs.ld (d := Random.oUsedPtr) (by decide), hs.ld (d := Random.oUsed) (by decide), hu]
  · apply two_taint [.x2] ?_ (by taint_decide)
    intro p s t hs ht r hr
    rw [List.mem_singleton] at hr
    subst r
    exact hs.2.trans ht.2.symm

theorem random_finish_ct : RelCT isa (Two RandomFinishPre) RandomSign.finish (fun _ _ => True) := by
  unfold RandomSign.finish
  refine RelCT.seq (two_piece (Ψ := fun p s => RandomFinishPre p s ∧ (s.gpr .x4 == 0#64) = (p.status == 1))
    [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide) (fun _ _ h => header_ok h)) ?_
  refine RelCT.seq ?_ tail_ct
  refine two_ite (fun p s t hs ht => by
    change some (!(s.gpr .x4 == 0#64)) = some (!(t.gpr .x4 == 0#64))
    rw [hs.2, ht.2]) ?_ ?_
  · exact (two_post zero_ct (fun _ _ h => zero_tail h)).mono
      (fun _ _ h => two_mono (fun _ _ h => h.1.1) h) (fun _ _ h => h)
  · exact RelCT.block_nil (fun _ _ h => two_mono (fun _ _ h => ⟨h.1.1.scr, h.1.1.sp, h.1.1.usedPtr⟩) h)

end VG.Proof.Dsa.AArch64
