import VerifiedGarbage.Proof.Seed.X86_64.KeyRounds
import VerifiedGarbage.Proof.Seed.X86_64.Copy
import VerifiedGarbage.Proof.Seed.Memory

/-!
# Loading the key on x86-64

`keyLoad_ok`: `keyLoad` puts the key's big-endian words in `r10 = Key0 || Key1`
and `r11 = Key2 || Key3` (`kx`, `ky` of `keyWords key 0`).
-/

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Seed.X86_64 VG.Proof.Seed

theorem step_mov32_mem {s : State} (d : Reg) {m : MemOp} (h : InRegions (s.rd ++ s.wr) (s.ea m) 4) :
    ∃ t, exec (.mov32 d (.mem m)) s = some t ∧ Upd s t d ((s.mem.readW (s.ea m) 32).setWidth 64) :=
  ⟨_, exec_mov32_mem h, upd_of rfl⟩

theorem step_bswap32 (s : State) (d : Reg) :
    ∃ t, exec (.bswap32 d) s = some t ∧ Upd s t d ((bswap32 ((s.gpr d).setWidth 32)).setWidth 64) :=
  ⟨_, rfl, upd_of rfl⟩

theorem step_shl (s : State) (d : Reg) {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 63) :
    ∃ t, exec (.shift .shl d n) s = some t ∧ Upd s t d (s.gpr d <<< n) := by
  refine ⟨_, ?_, upd_flags (some ((s.gpr d).getLsbD (64 - n)))
    (if n = 1 then some ((s.gpr d <<< n).msb ^^ (s.gpr d).getLsbD (64 - n)) else none)
    (some (s.gpr d <<< n == 0)) (some (s.gpr d <<< n).msb) rfl⟩
  simp only [exec, execShift, h1, h2, and_self, ite_true]

theorem step_or_reg (s : State) (d r : Reg) :
    ∃ t, exec (.alu .or d (.reg r)) s = some t ∧ Upd s t d (s.gpr d ||| s.gpr r) :=
  ⟨_, rfl, ⟨fun x => by rw [gpr_setReg, gpr_arithFlags], rfl, rfl, rfl⟩⟩

/-- `keyLoad2 d k`: the key's big-endian words `k` and `k + 4`, into `d`. -/
theorem keyLoad2_ok {s : State} {d : Reg} (hd : d ≠ .rax) {k : Nat} (hk : k ≤ 8)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 k) 4)
    (hr' : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (k + 4)) 4) :
    ∃ t, runBlock isa (keyLoad2 d k) s = some t ∧
      t.gpr d = Spec.Seed.wordAt (Spec.Seed.blockAt s.mem (s.gpr .rdi)) k ++
        Spec.Seed.wordAt (Spec.Seed.blockAt s.mem (s.gpr .rdi)) (k + 4) ∧
      (∀ r, r ≠ .rax → r ≠ d → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨s1, e1, u1⟩ := step_mov32_mem (s := s) .rax (m := { base := .rdi, disp := ((k : Nat) : Int) })
    (by rw [ea_off]; exact hr)
  obtain ⟨s2, e2, u2⟩ := step_bswap32 s1 .rax
  obtain ⟨s3, e3, u3⟩ := step_shl s2 .rax (n := 32) (by decide) (by decide)
  have rdi3 : s3.gpr .rdi = s.gpr .rdi := by
    rw [u3.other (by decide), u2.other (by decide), u1.other (by decide)]
  obtain ⟨s4, e4, u4⟩ := step_mov32_mem (s := s3) d (m := { base := .rdi, disp := ((k + 4 : Nat) : Int) })
    (by rw [ea_off, rdi3, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hr')
  obtain ⟨s5, e5, u5⟩ := step_bswap32 s4 d
  obtain ⟨s6, e6, u6⟩ := step_or_reg s5 d .rax
  refine ⟨s6, ?_, ?_, fun r ha hr => ?_, ?_, ?_, ?_⟩
  · rw [keyLoad2, runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_cons, e3,
      runStep_some, runBlock_cons, e4, runStep_some, runBlock_cons, e5, runStep_some, runBlock_cons, e6,
      runStep_some, runBlock_nil]
  · have m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
    rw [u6.self, u5.self, u4.self, setWidth_setWidth_32, u5.other (Ne.symm hd), u4.other (Ne.symm hd),
      u3.self, u2.self, u1.self, setWidth_setWidth_32, ea_off, ea_off, rdi3, m3,
      wordAt_blockAt _ _ (by omega), wordAt_blockAt _ _ (by omega), BitVec.or_comm]
    have := BitVec.setWidth_append_eq_shiftLeft_setWidth_or (w'' := 64)
      (b := byteRev32 (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 k) 32))
      (b' := byteRev32 (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (k + 4)) 32))
    rw [BitVec.setWidth_eq] at this
    rw [this]
    rfl
  · rw [u6.other hr, u5.other hr, u4.other hr, u3.other ha, u2.other ha, u1.other ha]
  · rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · rw [u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]

end VG.Proof.Seed.X86_64
