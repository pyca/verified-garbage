module
public import VerifiedGarbage.Impl.Seed.PPC64LE.ExpandKey
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Seed.Memory

import VerifiedGarbage.Proof.Seed.PPC64LE.KeyRound
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Seed.SboxLit
import VerifiedGarbage.Proof.Framework.PPC64LE.Straight
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Seed

/-!
# Loading the key on PPC64LE

`keyLoad2_ok`: `keyLoad2 d k` puts the key's big-endian words `k` and
`k + 4` in `d = Key_k || Key_k+1`.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Impl.Seed.PPC64LE VG.Proof.Seed

theorem keyLoad2_ok {s : State} {d : Reg} (hd : d ≠ .r9) (hd3 : d ≠ .r3) {k : Nat} (hk : k ≤ 8) (hk4 : k % 4 = 0)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 k) 4)
    (hr' : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (k + 4)) 4) :
    ∃ t, runBlock isa (keyLoad2 d k) s = some t ∧
      t.gpr d = Spec.Seed.wordAt (Spec.Seed.blockAt s.mem (s.gpr .r3)) k ++
        Spec.Seed.wordAt (Spec.Seed.blockAt s.mem (s.gpr .r3)) (k + 4) ∧
      (∀ r, r ≠ .r9 → r ≠ d → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp := by
  let W0 := s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 k) 32
  let W1 := s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 (k + 4)) 32
  obtain ⟨s1, e1, u1⟩ := step_x s (.li .r9 k) .r9 (BitVec.ofNat 64 k) (exec_li (by omega))
  obtain ⟨s2, e2, u2⟩ := step_x s1 (.loadRev .w .r9 .r3 .r9) .r9 ((rev32 W0).setWidth 64)
    (by rw [exec_loadRev_w (by decide) (by rw [u1.self, u1.other (by decide), u1.rd, u1.wr]; exact hr),
      u1.self, u1.other (by decide), u1.mem])
  obtain ⟨s3, e3, u3⟩ := step_x s2 (.lsl .r9 .r9 32) .r9 (s2.gpr .r9 <<< 32) (exec_lsl (by decide))
  have r3₃ : s3.gpr .r3 = s.gpr .r3 := by rw [u3.other (by decide), u2.other (by decide), u1.other (by decide)]
  have m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  obtain ⟨s4, e4, u4⟩ := step_x s3 (.li d (k + 4)) d (BitVec.ofNat 64 (k + 4)) (exec_li (by omega))
  have r3₄ : s4.gpr .r3 = s.gpr .r3 := by rw [u4.other (Ne.symm hd3), r3₃]
  have hr4 : InRegions (s4.rd ++ s4.wr) (s4.gpr .r3 + s4.gpr d) 4 := by
    rw [u4.self, r3₄, u4.rd, u4.wr, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hr'
  obtain ⟨s5, e5, u5⟩ := step_x s4 (.loadRev .w d .r3 d) d ((rev32 W1).setWidth 64)
    (by rw [exec_loadRev_w (by decide) hr4, u4.self, r3₄, u4.mem, m3])
  obtain ⟨s6, e6, u6⟩ := step_x s5 (.logic .or d d .r9) d (s5.gpr d ||| s5.gpr .r9) exec_logic
  refine ⟨s6, ?_, ?_, fun r ha hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [keyLoad2, runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_cons, e3,
      runStep_some, runBlock_cons, e4, runStep_some, runBlock_cons, e5, runStep_some, runBlock_cons, e6,
      runStep_some, runBlock_nil]
  · rw [u6.self, u5.self, u5.other (Ne.symm hd), u4.other (Ne.symm hd), u3.self, u2.self,
      wordAt_blockAt _ _ (by omega), wordAt_blockAt _ _ (by omega), BitVec.or_comm,
      show rev32 = byteRev32 from rfl]
    have := BitVec.setWidth_append_eq_shiftLeft_setWidth_or (w'' := 64) (b := byteRev32 W0) (b' := byteRev32 W1)
    rw [BitVec.setWidth_eq] at this
    rw [this]
  · rw [u6.other hr, u5.other hr, u4.other hr, u3.other ha, u2.other ha, u1.other ha]
  · rw [u6.mem, u5.mem, u4.mem, m3]
  · rw [u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
  · rw [u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp]

end VG.Proof.Seed.PPC64LE
