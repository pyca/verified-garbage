module

public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# AArch64: reading a state after a write, for symbolic execution

The registers of a state after a write, read one write at a time, with
`State.write` kept folded, as in `VG.X86_64.RegUpd` (which explains why):
`gpr_write` for registers that are literals, `gpr_write_self` and
`gpr_write_of_ne` for variables.
-/

@[expose] public section

namespace VG.AArch64.RegUpd

variable (s : State)

theorem gpr_write (sz : Size) (d : Reg) (v : BitVec sz.bits) (r : Reg) :
    (s.write sz d v).gpr r = if r = d then v.setWidth 64 else s.gpr r := rfl

theorem gpr_write_self (sz : Size) (r : Reg) (v : BitVec sz.bits) :
    (s.write sz r v).gpr r = v.setWidth 64 := by
  simp [State.write]

theorem gpr_write_of_ne (sz : Size) {r r' : Reg} (v : BitVec sz.bits) (h : ¬r' = r) :
    (s.write sz r v).gpr r' = s.gpr r' := by
  simp [State.write, h]

theorem mem_write (sz : Size) (r : Reg) (v : BitVec sz.bits) : (s.write sz r v).mem = s.mem := rfl
theorem rd_write (sz : Size) (r : Reg) (v : BitVec sz.bits) : (s.write sz r v).rd = s.rd := rfl
theorem wr_write (sz : Size) (r : Reg) (v : BitVec sz.bits) : (s.write sz r v).wr = s.wr := rfl
theorem sp_write (sz : Size) (r : Reg) (v : BitVec sz.bits) : (s.write sz r v).sp = s.sp := rfl
theorem c_write (sz : Size) (r : Reg) (v : BitVec sz.bits) : (s.write sz r v).c = s.c := rfl
theorem nf_write (sz : Size) (r : Reg) (v : BitVec sz.bits) : (s.write sz r v).nf = s.nf := rfl
theorem zf_write (sz : Size) (r : Reg) (v : BitVec sz.bits) : (s.write sz r v).zf = s.zf := rfl
theorem vf_write (sz : Size) (r : Reg) (v : BitVec sz.bits) : (s.write sz r v).vf = s.vf := rfl

theorem gpr_addWithCarry (sz : Size) (d : Reg) (a b : BitVec sz.bits) (c : Bool) (r : Reg) :
    (s.addWithCarry sz d a b c).gpr r =
      if r = d then (a + b + BitVec.ofNat sz.bits c.toNat).setWidth 64 else s.gpr r := rfl

theorem c_addWithCarry (sz : Size) (d : Reg) (a b : BitVec sz.bits) (c : Bool) :
    (s.addWithCarry sz d a b c).c = decide (2 ^ sz.bits ≤ a.toNat + b.toNat + c.toNat) := rfl

theorem mem_addWithCarry (sz : Size) (d : Reg) (a b : BitVec sz.bits) (c : Bool) :
    (s.addWithCarry sz d a b c).mem = s.mem := rfl
theorem rd_addWithCarry (sz : Size) (d : Reg) (a b : BitVec sz.bits) (c : Bool) :
    (s.addWithCarry sz d a b c).rd = s.rd := rfl
theorem wr_addWithCarry (sz : Size) (d : Reg) (a b : BitVec sz.bits) (c : Bool) :
    (s.addWithCarry sz d a b c).wr = s.wr := rfl
theorem sp_addWithCarry (sz : Size) (d : Reg) (a b : BitVec sz.bits) (c : Bool) :
    (s.addWithCarry sz d a b c).sp = s.sp := rfl

theorem v_write (sz : Size) (r : Reg) (x : BitVec sz.bits) : (s.write sz r x).v = s.v := rfl

theorem v_setV (d : VReg) (x : BitVec 128) (r : VReg) :
    (s.setV d x).v r = if r = d then x else s.v r := rfl

theorem v_setV_self (r : VReg) (x : BitVec 128) : (s.setV r x).v r = x := by
  simp [State.setV]

theorem v_setV_of_ne {r r' : VReg} (x : BitVec 128) (h : r' ≠ r) :
    (s.setV r x).v r' = s.v r' := by simp [State.setV, h]

theorem gpr_setV (r : VReg) (x : BitVec 128) : (s.setV r x).gpr = s.gpr := rfl
theorem mem_setV (r : VReg) (x : BitVec 128) : (s.setV r x).mem = s.mem := rfl
theorem rd_setV (r : VReg) (x : BitVec 128) : (s.setV r x).rd = s.rd := rfl
theorem wr_setV (r : VReg) (x : BitVec 128) : (s.setV r x).wr = s.wr := rfl
theorem sp_setV (r : VReg) (x : BitVec 128) : (s.setV r x).sp = s.sp := rfl

end VG.AArch64.RegUpd

namespace VG.AArch64

/-- A successful `ldp` writes its two registers and nothing else. -/
theorem exec_ldp_eq {t1 t2 n : Reg} {off : Nat} {s s' : State} (h : exec (.ldp t1 t2 n off) s = some s') :
    ∃ v₁ v₂ : BitVec 64, s' = (s.write .x t1 v₁).write .x t2 v₂ := by
  obtain ⟨-, h⟩ := Option.ite_none_right_eq_some.mp h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, -, _, -, rfl⟩ := h
  exact ⟨_, _, rfl⟩

/-- A successful `stp` changes memory and nothing else. -/
theorem exec_stp_eq {t1 t2 n : Reg} {off : Nat} {s s' : State} (h : exec (.stp t1 t2 n off) s = some s') :
    ∃ m : Mem, s' = { s with mem := m } := by
  obtain ⟨-, h⟩ := Option.ite_none_right_eq_some.mp h
  simp only [Option.bind_eq_some_iff, State.store] at h
  obtain ⟨_, h₁, h₂⟩ := h
  split at h₁ <;> cases h₁
  split at h₂ <;> cases h₂
  exact ⟨_, rfl⟩

end VG.AArch64
