module

import VerifiedGarbage.Proof.EcKey.Compressed.Parity
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Ecdsa.Arm.Finish
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.TCB.Code

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass
open VG.Proof.Ecdsa.Arm VG.Impl.Ecdsa.Arm


open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_strb op2_imm op2_reg dpVal)

theorem tag32_byte (m : Mem) (base : Addr) (a n : Nat) (hn : 0 < n) (b : Bool) :
    ((((m.readW (off base a) 32 &&& 1) ||| 2) &&& mask32 (b = true)).setWidth 8) =
      if b then BitVec.ofNat 8 (2 + wordsVal m base a n % 2) else 0 := by
  rw [word32_parity m base a n hn]
  rcases Nat.mod_two_eq_zero_or_one (wordsVal m base a n) with h | h <;>
    cases b <;> simp [h, mask32] <;> decide

theorem tag_ok {c : Cfg} {s : State} {base : Addr} (hs : Scr s base size)
    (hy : c.sl Impl.Ecdh.Arm.QY + 4 ≤ size) {o : BitVec 32}
    (hout : s.gpr .lr = o) (hfit : o.toNat + 1 ≤ 2 ^ 32)
    (hw : InRegions s.wr (State.addr o) 1) (b : Bool)
    (hf : s.gpr .r10 = mask32 (b = true)) (hn : 0 < c.n) :
    WP isa (.block (Impl.EcKey.Compressed.Arm.compressTag c)) s fun t =>
      t.mem (State.addr o) =
        (if b then BitVec.ofNat 8 (2 + sv c base s Impl.Ecdh.Arm.QY % 2) else 0) ∧
      Outside (State.addr o) 0 1 s.mem t.mem ∧ Rest [.r4] s t := by
  unfold Impl.EcKey.Compressed.Arm.compressTag
  refine wp_ldr (hs.off_lt (by omega)) (hs.ea (by omega)) (hs.read hy) fun s₁ u₁ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₂ u₂ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₃ u₃ => ?_
  refine wp_dp (op2_reg _ _) fun s₄ u₄ => ?_
  have k : Rest [.r4] s s₄ := (u₁.rest (by simp)).trans
    ((u₂.rest (by simp)).trans ((u₃.rest (by simp)).trans (u₄.rest (by simp))))
  have hm : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have ho : s₄.gpr .lr = o := (k.gpr _ (by decide)).trans hout
  have ht : (s₄.gpr .r4).setWidth 8 =
      if b then BitVec.ofNat 8 (2 + sv c base s Impl.Ecdh.Arm.QY % 2) else 0 := by
    rw [u₄.gpr, dpVal, u₃.gpr, dpVal, u₂.gpr, dpVal, u₁.gpr,
      u₃.other .r10 (by decide), u₂.other .r10 (by decide), u₁.other .r10 (by decide), hf]
    exact tag32_byte _ _ _ _ hn b
  refine wp_strb (by decide) (a := State.addr o)
    (by rw [ho, addr_add (by omega)]; simp) (by rw [k.wr]; exact hw) fun t mt => ?_
  refine WP.block_nil ⟨?_, ?_, k.trans (mt.rest _)⟩
  · rw [mt.mem, writeW8_self, ht]
  · rw [mt.mem, ← hm]
    simpa [off] using
      (writeW8_outside s₄.mem (State.addr o) (d := 0) ((s₄.gpr .r4).setWidth 8) (by decide))

end VG.Proof.EcKey.Compressed.Arm
