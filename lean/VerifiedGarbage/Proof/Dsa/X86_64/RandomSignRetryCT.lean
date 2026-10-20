module
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Impl.Dsa.X86_64.RandomSign

import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Order.RelClasses
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
public import Aesop.BuiltinRules
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Impl.Dsa.X86_64.RandomSign
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
meta import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Order.RelClasses
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Mathlib.Tactic.Push
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.Attr.Core
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! Retry control reveals only the signer's low-word success bit and attempt budget. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

structure RandomRetryPublic where
  B : Addr
  success : Bool
  attempts : Nat

def RandomRetryPre (p : RandomRetryPublic) (s : State) : Prop :=
  Scr s p.B Random.frameBytes ∧ s.gpr .rsp = p.B ∧
  (s.gpr .rax).setWidth 32 = (if p.success then 1 else 0) ∧
  word s.mem p.B Random.oAttempts = BitVec.ofNat 64 p.attempts ∧
  0 < p.attempts ∧ p.attempts < 2 ^ 64

def RandomRetryMid (p : RandomRetryPublic) (s : State) : Prop :=
  Scr s p.B Random.frameBytes ∧ s.gpr .rsp = p.B ∧ s.zf = some (!p.success) ∧
  word s.mem p.B Random.oAttempts = BitVec.ofNat 64 p.attempts ∧
  0 < p.attempts ∧ p.attempts < 2 ^ 64

private theorem header_ok {p : RandomRetryPublic} {s : State} (h : RandomRetryPre p s) :
    WP isa (.block [.mov32 .rax (.reg .rax), .store (Random.sp Random.oStatus) .rax,
      .alu .cmp .rax (.imm 0)]) s (RandomRetryMid p) := by
  obtain ⟨hs, hsp, ha, hn, hp, hb⟩ := h
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = s.mem.writeW (off p.B Random.oStatus) (if p.success then (1 : BitVec 64) else 0) ∧
      t.zf = some (!p.success)) (by
      cases hx : p.success <;> xrun [random_ea_sp, hsp, hs.st (d := Random.oStatus) (by decide), hx, ha] <;> rfl) rfl)
    fun t ⟨⟨hm, hz⟩, hk⟩ => ?_
  refine ⟨hs.congr hk.2.2, (hk.gpr (by decide)).trans hsp, hz, ?_, hp, hb⟩
  rw [hm, (writeW_outside _ p.B _ (by decide)).word (by decide) (by decide)]
  exact hn

private theorem decrement_ok {p : RandomRetryPublic} {s : State} (h : RandomRetryMid p s) :
    WP isa (.block [.mov .rax (.mem (Random.sp Random.oAttempts)), .alu .sub .rax (.imm 1),
      .store (Random.sp Random.oAttempts) .rax]) s fun t =>
      t.gpr .rsp = p.B ∧ t.zf = some (decide (p.attempts = 1)) := by
  obtain ⟨hs, hsp, _, hn, hp, hb⟩ := h
  have hz : (BitVec.ofNat 64 (p.attempts - 1) == 0) = decide (p.attempts = 1) := by
    rw [ofNat64_beq_zero (by omega)]
    exact decide_eq_decide.mpr (by omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (p.attempts = 1)))
    (by xrun [random_ea_sp, hsp, hs.ld (d := Random.oAttempts) (by decide),
      hs.st (d := Random.oAttempts) (by decide), hn, ofNat64_pred hp hb, hz]) rfl)
    fun _ ⟨ht, hk⟩ => ⟨(hk.gpr (by decide)).trans hsp, ht⟩

theorem random_callFinish_ct : RelCT isa (Two RandomRetryPre) RandomSign.callFinish (fun _ _ => True) := by
  unfold RandomSign.callFinish
  refine RelCT.seq (two_piece (Ψ := RandomRetryMid) [.rsp] ?_ (by taint_decide)
    (fun _ _ h => header_ok h)) ?_
  · intro p s t hs ht r hr
    rw [List.mem_singleton] at hr
    subst r
    exact hs.2.1.trans ht.2.1.symm
  · refine two_ite (fun p s t hs ht => by simp only [eval, hs.2.2.1, ht.2.2.1]) ?_ ?_
    · refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .rsp = p.B ∧
        s.zf = some (decide (p.attempts = 1))) [.rsp] ?_ (by taint_decide)
        (fun _ _ h => decrement_ok h.1)) ?_
      · intro p s t hs ht r hr
        rw [List.mem_singleton] at hr
        subst r
        exact hs.1.2.1.trans ht.1.2.1.symm
      · refine two_ite (fun p s t hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
        · apply two_taint [.rsp] ?_ (by taint_decide)
          intro p s t hs ht r hr
          rw [List.mem_singleton] at hr
          subst r
          exact hs.1.1.trans ht.1.1.symm
        · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)
    · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)

end VG.Proof.Dsa.X86_64
