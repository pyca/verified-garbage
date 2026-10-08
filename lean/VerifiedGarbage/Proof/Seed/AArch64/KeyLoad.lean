import VerifiedGarbage.Proof.Seed.AArch64.KeyRounds
import VerifiedGarbage.Proof.Seed.Memory

/-!
# Loading the key on AArch64

`keyLoad2_ok`: `keyLoad2 d k` puts the key's big-endian words `k` and
`k + 4` in `d = Key_k || Key_k+1`.
-/

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.Seed.AArch64 VG.Impl.Aes.AArch64
  VG.Proof.Seed

theorem keyLoad2_ok {s : State} {d : Reg} (hd : d ≠ .x14) {k : Nat} (hk : k ≤ 8) (hk4 : k % 4 = 0)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 k) 4)
    (hr' : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (k + 4)) 4) :
    ∃ t, runBlock isa (keyLoad2 d k) s = some t ∧
      t.gpr d = Spec.Seed.wordAt (Spec.Seed.blockAt s.mem (s.gpr .x0)) k ++
        Spec.Seed.wordAt (Spec.Seed.blockAt s.mem (s.gpr .x0)) (k + 4) ∧
      (∀ r, r ≠ .x14 → r ≠ d → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp := by
  let W0 := s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 k) 32
  let W1 := s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (k + 4)) 32
  obtain ⟨s1, e1, u1⟩ := step_w s (.ldr .w .x14 .x0 k) .x14 W0 (exec_ldr_w ⟨hk4, by omega⟩ hr)
  obtain ⟨s2, e2, u2⟩ := step_w s1 (.rev32 .x14 .x14) .x14 (rev32 (s1.read .w .x14)) rfl
  obtain ⟨s3, e3, u3⟩ := step_x s2 (.lsl .x .x14 .x14 32) .x14 (s2.read .x .x14 <<< 32)
    (by simp only [exec, show 32 < Size.x.bits by decide, ite_true])
  have x0₃ : s3.gpr .x0 = s.gpr .x0 := by rw [u3.other (by decide), u2.other (by decide), u1.other (by decide)]
  have m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  obtain ⟨s4, e4, u4⟩ := step_w s3 (.ldr .w d .x0 (k + 4)) d W1
    (by rw [exec_ldr_w ⟨by omega, by omega⟩ (by rw [x0₃, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hr'), x0₃, m3])
  obtain ⟨s5, e5, u5⟩ := step_w s4 (.rev32 d d) d (rev32 (s4.read .w d)) rfl
  obtain ⟨s6, e6, u6⟩ := step_x s5 (orrR d d .x14) d (s5.gpr d ||| s5.gpr .x14)
    (by simp [orrR, exec, State.read])
  refine ⟨s6, ?_, ?_, fun r ha hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [keyLoad2, runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_cons, e3,
      runStep_some, runBlock_cons, e4, runStep_some, runBlock_cons, e5, runStep_some, runBlock_cons, e6,
      runStep_some, runBlock_nil]
  · rw [u6.self, u5.self, u5.other (Ne.symm hd), u4.other (Ne.symm hd), u3.self]
    simp only [State.read, Size.bits, BitVec.setWidth_eq]
    rw [u4.self, setWidth_setWidth_32, u2.self]
    simp only [State.read, Size.bits]
    rw [u1.self, setWidth_setWidth_32,
      wordAt_blockAt _ _ (by omega), wordAt_blockAt _ _ (by omega), BitVec.or_comm]
    have := BitVec.setWidth_append_eq_shiftLeft_setWidth_or (w'' := 64) (b := byteRev32 W0) (b' := byteRev32 W1)
    rw [BitVec.setWidth_eq] at this
    rw [this]
    rfl
  · rw [u6.other hr, u5.other hr, u4.other hr, u3.other ha, u2.other ha, u1.other ha]
  · rw [u6.mem, u5.mem, u4.mem, m3]
  · rw [u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
  · rw [u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp]

end VG.Proof.Seed.AArch64
