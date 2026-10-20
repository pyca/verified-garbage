module
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign

import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRetry
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRetry
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! Retry control reveals only the signer's low-word success bit and attempt budget. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

structure RandomRetryPublic where
  B : Addr
  success : Bool
  attempts : Nat

def RandomRetryPre (p : RandomRetryPublic) (s : State) : Prop :=
  Scr s p.B Random.frameBytes ∧ s.sp = p.B ∧
  (s.gpr .x0).setWidth 32 = (if p.success then 1 else 0) ∧
  word s.mem p.B Random.oAttempts = BitVec.ofNat 64 p.attempts ∧
  0 < p.attempts ∧ p.attempts < 2 ^ 64

def RandomRetryMid (p : RandomRetryPublic) (s : State) : Prop :=
  Scr s p.B Random.frameBytes ∧ s.sp = p.B ∧
  s.gpr .x0 = (if p.success then (1 : BitVec 64) else 0) ∧
  word s.mem p.B Random.oAttempts = BitVec.ofNat 64 p.attempts ∧
  0 < p.attempts ∧ p.attempts < 2 ^ 64

private theorem header_ok {p : RandomRetryPublic} {s : State} (h : RandomRetryPre p s) :
    WP isa (.block (([.ldrSp .x30 RandomSign.oLink, .logic .orr .w .x0 .x0 .x0] : List Instr) ++
      Random.store Random.oStatus .x0)) s (RandomRetryMid p) := by
  obtain ⟨hs, hsp, ha, hn, hp, hb⟩ := h
  refine WP.mono (random_retryHead_ok p.success hs hsp ha) fun t ⟨hm, hx, _, hk⟩ => ?_
  refine ⟨hs.congr hk.wr, hk.sp.trans hsp, hx, ?_, hp, hb⟩
  rw [hm, (writeW_outside _ p.B _ (by decide)).word (by decide) (by decide)]
  exact hn

private theorem decrement_ok {p : RandomRetryPublic} {s : State} (h : RandomRetryMid p s) :
    WP isa (.block (([.ldrSp .x0 Random.oAttempts, .subImm .x .x0 .x0 1] : List Instr) ++
      Random.store Random.oAttempts .x0)) s fun t =>
      t.sp = p.B ∧ t.gpr .x0 = BitVec.ofNat 64 (p.attempts - 1) := by
  obtain ⟨hs, hsp, _, hn, hp, hb⟩ := h
  exact WP.mono (random_attemptDecrement_ok hs hsp hn hp hb)
    (fun _ ⟨_, hx, hk⟩ => ⟨hk.sp.trans hsp, hx⟩)

theorem random_callFinish_ct : RelCT isa (Two RandomRetryPre) RandomSign.callFinish (fun _ _ => True) := by
  unfold RandomSign.callFinish
  refine RelCT.seq (two_piece (Ψ := RandomRetryMid) [] (by intro _ _ _ _ _ _ h; cases h)
    (by taint_decide) (fun _ _ h => header_ok h)) ?_
  refine two_ite (fun p s t hs ht => by simp only [eval, State.read, hs.2.2.1, ht.2.2.1]) ?_ ?_
  · refine RelCT.seq (two_piece (Ψ := fun p s => s.sp = p.B ∧
      s.gpr .x0 = BitVec.ofNat 64 (p.attempts - 1)) []
      (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)
      (fun _ _ h => decrement_ok h.1)) ?_
    refine two_ite (fun p s t hs ht => by simp only [eval, State.read, hs.2, ht.2]) ?_ ?_
    · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)
    · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)
  · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)

end VG.Proof.Dsa.AArch64
