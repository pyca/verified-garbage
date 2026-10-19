module
public import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinish
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignZero
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinish
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignZero
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

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
